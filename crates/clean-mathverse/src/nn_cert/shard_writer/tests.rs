// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the NN certificate shard writer.

use super::*;
use crate::nn_cert::types::{
    Activation, CertificateData, InputRegion, LayerKind, LayerSpec, LpNorm, NetworkSpec,
    OutputConstraint, ProofType, RobustnessProperty, VerifierTool,
};
use crate::shard::ShardReader;
use crate::types::AxiomProfile;

fn sample_cert() -> NNVerificationCert {
    NNVerificationCert {
        network_name: "test_net".to_string(),
        property: RobustnessProperty {
            input_region: InputRegion::EpsilonBall {
                epsilon: 0.01,
                norm: LpNorm::Linf,
                center: vec![],
            },
            output_constraint: OutputConstraint::ClassificationPreserved { original_class: 3 },
        },
        verifier_tool: VerifierTool::GammaCrown,
        result: VerificationResult::Verified,
        certificate_data: CertificateData {
            proof_type: ProofType::BoundPropagation,
            bounds: vec![],
            intermediate_results: vec![],
        },
        network_spec: NetworkSpec {
            input_dim: 28,
            output_dim: 10,
            layers: vec![
                LayerSpec {
                    kind: LayerKind::Dense,
                    input_dim: 28,
                    output_dim: 64,
                },
                LayerSpec {
                    kind: LayerKind::Dense,
                    input_dim: 64,
                    output_dim: 10,
                },
            ],
            activation: Activation::ReLU,
        },
    }
}

#[test]
fn test_write_nn_certs_to_writer_single_cert() {
    let cert = sample_cert();
    let mut writer = ShardWriter::new();
    let stats = write_nn_certs_to_writer(&[cert], &mut writer);

    assert_eq!(stats.total_parsed, 1);
    assert_eq!(stats.verified_count, 1);
    assert_eq!(stats.entries_written, 3);

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("shard write");
    let reader = ShardReader::from_bytes(&buf).expect("shard read");

    assert_eq!(reader.header.constant_count, 3);
    assert!(reader.lookup_name("test_net.NetworkType").is_some());
    assert!(reader.lookup_name("test_net.RobustnessProperty").is_some());
    assert!(reader.lookup_name("test_net.Proof").is_some());
}

#[test]
fn test_write_nn_certs_to_writer_empty() {
    let mut writer = ShardWriter::new();
    let stats = write_nn_certs_to_writer(&[], &mut writer);
    assert_eq!(stats.total_parsed, 0);
    assert_eq!(stats.entries_written, 0);
}

#[test]
fn test_write_nn_certs_to_writer_axiom_profile() {
    let mut writer = ShardWriter::new();
    write_nn_certs_to_writer(&[sample_cert()], &mut writer);

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write");
    let reader = ShardReader::from_bytes(&buf).expect("read");

    let (_, hdr) = reader.lookup_name("test_net.Proof").expect("proof");
    assert!(hdr.axiom_profile.has(AxiomProfile::FLOAT_APPROX));
    assert!(hdr.axiom_profile.has(AxiomProfile::NN_ABSTRACTION));
    assert!(hdr.axiom_profile.is_trust_gated());
}

#[test]
fn test_write_nn_certs_to_writer_content_domain() {
    let mut writer = ShardWriter::new();
    write_nn_certs_to_writer(&[sample_cert()], &mut writer);

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write");
    let reader = ShardReader::from_bytes(&buf).expect("read");

    let (_, hdr) = reader.lookup_name("test_net.NetworkType").expect("type");
    assert_eq!(hdr.content_domain, ContentDomain::NnVerification as u8);
}

#[test]
fn test_write_nn_certs_to_writer_multiple_certs() {
    let mut cert1 = sample_cert();
    cert1.network_name = "net_a".to_string();

    let mut cert2 = sample_cert();
    cert2.network_name = "net_b".to_string();
    cert2.result = VerificationResult::Counterexample;

    let mut writer = ShardWriter::new();
    let stats = write_nn_certs_to_writer(&[cert1, cert2], &mut writer);

    assert_eq!(stats.total_parsed, 2);
    assert_eq!(stats.verified_count, 1);
    assert_eq!(stats.counterexample_count, 1);
    assert_eq!(stats.entries_written, 6);
}

#[test]
fn test_write_nn_certs_to_shard_roundtrip() {
    let cert = sample_cert();
    let dir = tempfile::tempdir().expect("temp dir");
    let shard_path = dir.path().join("nn_verif.mathverse");

    let stats = write_nn_certs_to_shard(&[cert], &shard_path).expect("should write shard");
    assert_eq!(stats.entries_written, 3);
    assert_eq!(stats.verified_count, 1);

    assert!(shard_path.exists());
    assert!(dir.path().join("nn_verif.mathverse.json").exists());

    let data = std::fs::read(&shard_path).expect("read shard");
    let reader = ShardReader::from_bytes(&data).expect("parse shard");
    assert_eq!(reader.header.constant_count, 3);

    let meta = crate::shard_metadata::load_metadata(&shard_path).expect("load metadata");
    assert_eq!(meta.system_name, "NNVerification");
    assert_eq!(meta.declaration_count, 3);
}

#[test]
fn test_sanitize_name() {
    assert_eq!(sanitize_name("mnist_relu"), "mnist_relu");
    assert_eq!(sanitize_name("net-v2"), "net_v2");
    assert_eq!(sanitize_name("a b/c"), "a_b_c");
    assert_eq!(sanitize_name("foo.bar"), "foo.bar");
}

#[test]
fn test_format_property_signature_classification() {
    let prop = RobustnessProperty {
        input_region: InputRegion::EpsilonBall {
            epsilon: 0.03,
            norm: LpNorm::Linf,
            center: vec![],
        },
        output_constraint: OutputConstraint::ClassificationPreserved { original_class: 5 },
    };
    let sig = format_property_signature(&prop);
    assert!(sig.contains("Linf"));
    assert!(sig.contains("0.03"));
    assert!(sig.contains("ClassPreserved(5)"));
}

#[test]
fn test_format_property_signature_neuron_bound() {
    let prop = RobustnessProperty {
        input_region: InputRegion::EpsilonBall {
            epsilon: 0.1,
            norm: LpNorm::L2,
            center: vec![],
        },
        output_constraint: OutputConstraint::NeuronBound {
            neuron_idx: 3,
            lower: Some(0.5),
            upper: None,
        },
    };
    let sig = format_property_signature(&prop);
    assert!(sig.contains("L2"));
    assert!(sig.contains("NeuronBound(3"));
}

#[test]
fn test_verified_cert_gets_translated_confidence() {
    let mut writer = ShardWriter::new();
    write_nn_certs_to_writer(&[sample_cert()], &mut writer);

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write");
    let reader = ShardReader::from_bytes(&buf).expect("read");

    let (_, hdr) = reader.lookup_name("test_net.Proof").expect("proof");
    assert_eq!(hdr.import_confidence, ImportConfidence::Translated as u8);
}

#[test]
fn test_counterexample_cert_gets_axiomatized_confidence() {
    let mut cert = sample_cert();
    cert.result = VerificationResult::Counterexample;
    let mut writer = ShardWriter::new();
    write_nn_certs_to_writer(&[cert], &mut writer);

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write");
    let reader = ShardReader::from_bytes(&buf).expect("read");

    let (_, hdr) = reader.lookup_name("test_net.Proof").expect("proof");
    assert_eq!(hdr.import_confidence, ImportConfidence::Axiomatized as u8);
}

#[test]
fn test_unknown_cert_gets_unverified_confidence() {
    let mut cert = sample_cert();
    cert.result = VerificationResult::Unknown;
    let mut writer = ShardWriter::new();
    write_nn_certs_to_writer(&[cert], &mut writer);

    let mut buf = Vec::new();
    writer.write(&mut buf).expect("write");
    let reader = ShardReader::from_bytes(&buf).expect("read");

    let (_, hdr) = reader.lookup_name("test_net.Proof").expect("proof");
    assert_eq!(hdr.import_confidence, ImportConfidence::Unverified as u8);
}
