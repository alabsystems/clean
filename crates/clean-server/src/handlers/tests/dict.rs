// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::external_cert::create_sample_certs;
use crate::handlers::*;
use clean_kernel::cert::ProofCert;

#[tokio::test]
async fn test_train_dict_basic() {
    let state = ServerState::new();
    let samples = create_sample_certs(10);

    let params = TrainDictParams {
        samples,
        max_size: None,
        level: None,
    };

    let response = handle_train_dict(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "Unexpected error: {:?}",
        response.error
    );

    let result: TrainDictResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert_eq!(result.sample_count, 10);
    assert!(result.size > 0, "Dictionary should have non-zero size");
    assert_eq!(result.target_level, 3); // Default level
    assert!(result.dict_id != 0, "Dictionary should have non-zero ID");
    assert!(
        !result.dictionary.is_empty(),
        "Dictionary base64 should not be empty"
    );
}

#[tokio::test]
async fn test_train_dict_custom_params() {
    let state = ServerState::new();
    let samples = create_sample_certs(10);

    let params = TrainDictParams {
        samples,
        max_size: Some(16 * 1024), // 16KB
        level: Some(5),
    };

    let response = handle_train_dict(&state, RequestId::Number(1), params).await;
    assert!(
        response.error.is_none(),
        "unexpected error: {:?}",
        response.error
    );

    let result: TrainDictResult = serde_json::from_value(response.result.unwrap()).unwrap();
    assert!(
        result.size <= 16 * 1024,
        "Dictionary should respect max_size"
    );
    assert_eq!(result.target_level, 5);
}

#[tokio::test]
async fn test_train_dict_not_enough_samples() {
    let state = ServerState::new();
    let samples = create_sample_certs(3); // Less than minimum 5

    let params = TrainDictParams {
        samples,
        max_size: None,
        level: None,
    };

    let response = handle_train_dict(&state, RequestId::Number(1), params).await;
    let error = response
        .error
        .expect("insufficient samples should produce an error");
    assert!(
        error.message.contains("Not enough samples") || error.message.contains("training failed"),
        "Expected not enough samples error, got: {}",
        error.message
    );
}

#[tokio::test]
async fn test_archive_cert_with_dict_basic() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let samples = create_sample_certs(10);

    // First train a dictionary
    let train_params = TrainDictParams {
        samples,
        max_size: None,
        level: None,
    };
    let train_response = handle_train_dict(&state, RequestId::Number(1), train_params).await;
    assert!(
        train_response.error.is_none(),
        "unexpected train error: {:?}",
        train_response.error
    );
    let train_result: TrainDictResult =
        serde_json::from_value(train_response.result.unwrap()).unwrap();

    // Now archive a certificate with the dictionary
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let archive_params = ArchiveCertWithDictParams {
        cert,
        dictionary: train_result.dictionary,
        level: None,
        include_stats: false,
    };

    let archive_response =
        handle_archive_cert_with_dict(&state, RequestId::Number(2), archive_params).await;
    assert!(
        archive_response.error.is_none(),
        "Unexpected error: {:?}",
        archive_response.error
    );

    let archive_result: ArchiveCertWithDictResult =
        serde_json::from_value(archive_response.result.unwrap()).unwrap();
    assert_eq!(archive_result.dict_id, train_result.dict_id);
    assert!(archive_result.original_size > 0);
    assert!(archive_result.compressed_size > 0);
    assert!(archive_result.compression_ratio > 0.0);
    assert!(!archive_result.archive.is_empty());
}

#[tokio::test]
async fn test_archive_cert_with_dict_with_stats() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let samples = create_sample_certs(10);

    // Train dictionary
    let train_params = TrainDictParams {
        samples,
        max_size: None,
        level: None,
    };
    let train_response = handle_train_dict(&state, RequestId::Number(1), train_params).await;
    let train_result: TrainDictResult =
        serde_json::from_value(train_response.result.unwrap()).unwrap();

    // Archive with stats
    let level = Level::zero();
    let cert = ProofCert::Sort {
        level: level.clone(),
    };

    let archive_params = ArchiveCertWithDictParams {
        cert,
        dictionary: train_result.dictionary,
        level: Some(5),
        include_stats: true,
    };

    let archive_response =
        handle_archive_cert_with_dict(&state, RequestId::Number(2), archive_params).await;
    assert!(
        archive_response.error.is_none(),
        "unexpected archive error: {:?}",
        archive_response.error
    );

    let archive_result: ArchiveCertWithDictResult =
        serde_json::from_value(archive_response.result.unwrap()).unwrap();
    assert!(
        archive_result.structure_shared_size.is_some(),
        "Stats should include structure_shared_size when include_stats=true"
    );
    assert_eq!(archive_result.compression_level, 5);
}

#[tokio::test]
async fn test_unarchive_cert_with_dict_roundtrip() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let samples = create_sample_certs(10);

    // Train dictionary
    let train_params = TrainDictParams {
        samples,
        max_size: None,
        level: None,
    };
    let train_response = handle_train_dict(&state, RequestId::Number(1), train_params).await;
    let train_result: TrainDictResult =
        serde_json::from_value(train_response.result.unwrap()).unwrap();

    // Create and archive certificate
    let level = Level::succ(Level::zero());
    let original_cert = ProofCert::Sort {
        level: level.clone(),
    };

    let archive_params = ArchiveCertWithDictParams {
        cert: original_cert.clone(),
        dictionary: train_result.dictionary.clone(),
        level: None,
        include_stats: false,
    };

    let archive_response =
        handle_archive_cert_with_dict(&state, RequestId::Number(2), archive_params).await;
    let archive_result: ArchiveCertWithDictResult =
        serde_json::from_value(archive_response.result.unwrap()).unwrap();

    // Unarchive
    let unarchive_params = UnarchiveCertWithDictParams {
        archive: archive_result.archive,
        dictionary: train_result.dictionary,
    };

    let unarchive_response =
        handle_unarchive_cert_with_dict(&state, RequestId::Number(3), unarchive_params).await;
    assert!(
        unarchive_response.error.is_none(),
        "Unexpected error: {:?}",
        unarchive_response.error
    );

    let unarchive_result: UnarchiveCertWithDictResult =
        serde_json::from_value(unarchive_response.result.unwrap()).unwrap();
    assert_eq!(unarchive_result.dict_id, train_result.dict_id);

    // Verify the certificate matches
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
async fn test_unarchive_cert_with_dict_invalid_dict() {
    let state = ServerState::new();

    let params = UnarchiveCertWithDictParams {
        archive: "SGVsbG8gV29ybGQ=".to_string(), // "Hello World" in base64
        dictionary: "bm90IGEgcmVhbCBkaWN0".to_string(), // Invalid dictionary
    };

    let response = handle_unarchive_cert_with_dict(&state, RequestId::Number(1), params).await;
    let error = response
        .error
        .expect("invalid dictionary should produce an error");
    assert!(
        error.message.contains("Invalid dictionary") || error.message.contains("Invalid archive"),
        "Expected format error, got: {}",
        error.message
    );
}

#[tokio::test]
async fn test_unarchive_cert_with_dict_wrong_dict() {
    use clean_kernel::Level;

    let state = ServerState::new();

    // Train two different dictionaries
    let samples1 = create_sample_certs(10);
    let samples2 = create_sample_certs(15); // Different sample count for variety

    let train_params1 = TrainDictParams {
        samples: samples1,
        max_size: Some(8 * 1024),
        level: Some(1),
    };
    let train_response1 = handle_train_dict(&state, RequestId::Number(1), train_params1).await;
    let train_result1: TrainDictResult =
        serde_json::from_value(train_response1.result.unwrap()).unwrap();

    let train_params2 = TrainDictParams {
        samples: samples2,
        max_size: Some(16 * 1024),
        level: Some(9),
    };
    let train_response2 = handle_train_dict(&state, RequestId::Number(2), train_params2).await;
    let train_result2: TrainDictResult =
        serde_json::from_value(train_response2.result.unwrap()).unwrap();

    // Archive with dict1
    let level = Level::zero();
    let cert = ProofCert::Sort { level };

    let archive_params = ArchiveCertWithDictParams {
        cert,
        dictionary: train_result1.dictionary,
        level: None,
        include_stats: false,
    };

    let archive_response =
        handle_archive_cert_with_dict(&state, RequestId::Number(3), archive_params).await;
    let archive_result: ArchiveCertWithDictResult =
        serde_json::from_value(archive_response.result.unwrap()).unwrap();

    // Try to unarchive with dict2 (wrong dictionary)
    let unarchive_params = UnarchiveCertWithDictParams {
        archive: archive_result.archive,
        dictionary: train_result2.dictionary,
    };

    let unarchive_response =
        handle_unarchive_cert_with_dict(&state, RequestId::Number(4), unarchive_params).await;
    assert!(
        unarchive_response.error.is_some(),
        "Should fail with wrong dictionary"
    );
}

#[tokio::test]
async fn test_dict_json_serialization() {
    use clean_kernel::Level;

    let state = ServerState::new();
    let samples = create_sample_certs(10);

    // Train dictionary
    let train_params = TrainDictParams {
        samples,
        max_size: None,
        level: None,
    };

    // Verify TrainDictParams can be serialized (for API usage)
    let params_json = serde_json::to_value(&train_params).unwrap();
    assert!(
        params_json.get("samples").is_some(),
        "serialized TrainDictParams should have 'samples' field"
    );

    let train_response = handle_train_dict(&state, RequestId::Number(1), train_params).await;
    let train_result: TrainDictResult =
        serde_json::from_value(train_response.result.unwrap()).unwrap();

    // Verify result can be re-serialized
    let result_json = serde_json::to_value(&train_result).unwrap();
    assert!(
        result_json.get("dictionary").is_some(),
        "TrainDictResult JSON should have 'dictionary' field"
    );
    assert!(
        result_json.get("dict_id").is_some(),
        "TrainDictResult JSON should have 'dict_id' field"
    );

    // Archive params serialization
    let level = Level::zero();
    let cert = ProofCert::Sort { level };

    let archive_params = ArchiveCertWithDictParams {
        cert,
        dictionary: train_result.dictionary.clone(),
        level: Some(5),
        include_stats: true,
    };

    let archive_params_json = serde_json::to_value(&archive_params).unwrap();
    assert!(
        archive_params_json.get("cert").is_some(),
        "ArchiveCertWithDictParams JSON should have 'cert' field"
    );
    assert!(
        archive_params_json.get("dictionary").is_some(),
        "ArchiveCertWithDictParams JSON should have 'dictionary' field"
    );
}

// ========================================================================
// getConfig Tests
// ========================================================================
