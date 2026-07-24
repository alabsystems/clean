// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use crate::handlers::*;
use clean_kernel::cert::ProofCert;

#[tokio::test]
async fn test_compress_cert_simple() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = CompressCertParams {
        cert,
        include_stats: false,
    };

    let response = handle_compress_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: CompressCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.stats.is_none(),
        "stats should be None when include_stats=false"
    );
}

#[tokio::test]
async fn test_compress_cert_with_stats() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = CompressCertParams {
        cert,
        include_stats: true,
    };

    let response = handle_compress_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: CompressCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    let stats = result
        .stats
        .expect("stats should be present when include_stats=true");
    assert!(stats.unique_levels >= 1);
}

#[tokio::test]
async fn test_compress_decompress_roundtrip() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let original_cert = ProofCert::Sort {
        level: level.clone(),
    };

    // Compress
    let compress_params = CompressCertParams {
        cert: original_cert.clone(),
        include_stats: false,
    };
    let compress_response =
        handle_compress_cert(&state, RequestId::Number(1), compress_params).await;
    assert!(
        compress_response.error.is_none(),
        "unexpected compress error: {:?}",
        compress_response.error
    );

    let compress_result: CompressCertResult =
        serde_json::from_value(compress_response.result.unwrap()).unwrap();

    // Decompress
    let decompress_params = DecompressCertParams {
        compressed: compress_result.compressed,
    };
    let decompress_response =
        handle_decompress_cert(&state, RequestId::Number(2), decompress_params).await;
    assert!(
        decompress_response.error.is_none(),
        "unexpected decompress error: {:?}",
        decompress_response.error
    );

    let decompress_result: DecompressCertResult =
        serde_json::from_value(decompress_response.result.unwrap()).unwrap();

    // Verify roundtrip - certificates should be equivalent
    match (&original_cert, &decompress_result.cert) {
        (ProofCert::Sort { level: l1 }, ProofCert::Sort { level: l2 }) => {
            assert!(
                Level::is_def_eq(l1, l2),
                "Levels should match after roundtrip"
            );
        }
        _ => panic!("Certificate type mismatch after roundtrip"),
    }
}

#[tokio::test]
async fn test_archive_cert_lz4() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = ArchiveCertParams {
        cert,
        algorithm: Some("lz4".to_string()),
        level: None,
        include_stats: false,
    };

    let response = handle_archive_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: ArchiveCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.algorithm, "lz4");
    assert!(result.original_size > 0);
    assert!(result.compressed_size > 0);
    assert!(!result.archive.is_empty());
}

#[tokio::test]
async fn test_archive_cert_zstd() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = ArchiveCertParams {
        cert,
        algorithm: Some("zstd".to_string()),
        level: None,
        include_stats: false,
    };

    let response = handle_archive_cert(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: ArchiveCertResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.algorithm, "zstd");
    assert!(result.original_size > 0);
}

#[tokio::test]
async fn test_archive_unarchive_roundtrip() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let original_cert = ProofCert::Sort {
        level: level.clone(),
    };

    // Archive
    let archive_params = ArchiveCertParams {
        cert: original_cert.clone(),
        algorithm: Some("lz4".to_string()),
        level: None,
        include_stats: false,
    };
    let archive_response = handle_archive_cert(&state, RequestId::Number(1), archive_params).await;
    assert!(
        archive_response.error.is_none(),
        "unexpected archive error: {:?}",
        archive_response.error
    );

    let archive_result: ArchiveCertResult =
        serde_json::from_value(archive_response.result.unwrap()).unwrap();

    // Unarchive
    let unarchive_params = UnarchiveCertParams {
        archive: archive_result.archive,
    };
    let unarchive_response =
        handle_unarchive_cert(&state, RequestId::Number(2), unarchive_params).await;
    assert!(
        unarchive_response.error.is_none(),
        "Unarchive error: {:?}",
        unarchive_response.error
    );

    let unarchive_result: UnarchiveCertResult =
        serde_json::from_value(unarchive_response.result.unwrap()).unwrap();

    assert_eq!(unarchive_result.algorithm, "lz4");

    // Verify roundtrip
    match (&original_cert, &unarchive_result.cert) {
        (ProofCert::Sort { level: l1 }, ProofCert::Sort { level: l2 }) => {
            assert!(
                Level::is_def_eq(l1, l2),
                "Levels should match after roundtrip"
            );
        }
        _ => panic!("Certificate type mismatch after roundtrip"),
    }
}

#[tokio::test]
async fn test_archive_invalid_algorithm() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let params = ArchiveCertParams {
        cert,
        algorithm: Some("invalid_algo".to_string()),
        level: None,
        include_stats: false,
    };

    let response = handle_archive_cert(&state, RequestId::Number(1), params).await;
    let err = response
        .error
        .expect("unknown algorithm should produce an error");
    assert!(
        err.message.contains("Unknown algorithm"),
        "error should mention 'Unknown algorithm', got: {}",
        err.message
    );
}

#[tokio::test]
async fn test_unarchive_invalid_base64() {
    let state = ServerState::new();

    let params = UnarchiveCertParams {
        archive: "not valid base64!!!".to_string(),
    };

    let response = handle_unarchive_cert(&state, RequestId::Number(1), params).await;
    let err = response
        .error
        .expect("invalid base64 should produce an error");
    assert!(
        err.message.contains("Invalid base64"),
        "error should mention 'Invalid base64', got: {}",
        err.message
    );
}
