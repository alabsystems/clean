// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, BTreeSet};

use trust_ir::{
    CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY,
    CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_OPERATIONS, CHC_X86_V8_I16_MASK_TO_BITS_COMPOSITION,
    CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS, CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    CHC_X86_V16_I8_MASK_TO_BITS_COMPOSITION, CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS,
    NativeSharedPrimitiveContractManifestRow, ProofDigest,
    chc_x86_hardware_vector_contract_manifest_digest,
    chc_x86_hardware_vector_contract_manifest_key_value_lines,
    chc_x86_hardware_vector_contract_manifest_key_value_text,
    chc_x86_hardware_vector_contract_manifest_row_count,
    chc_x86_hardware_vector_contract_manifest_rows,
    chc_x86_hardware_vector_contract_manifest_sha256,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_digest,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_lines,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_text,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_row_count,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_rows,
    petri_successor_trust_mc_chc_shared_primitive_contract_manifest_sha256,
    ty_shared_primitive_manifest_digest, ty_shared_primitive_manifest_key_value_lines,
    ty_shared_primitive_manifest_key_value_text, ty_shared_primitive_manifest_row_count,
    ty_shared_primitive_manifest_rows, ty_shared_primitive_manifest_sha256,
};

fn assert_sha256_shape(value: &str) {
    let hex = value
        .strip_prefix("sha256:")
        .expect("manifest SHA helper must use sha256: prefix");
    assert_eq!(hex.len(), 64, "manifest SHA helper must expose 32 bytes");
    assert!(
        hex.bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "manifest SHA helper must use lowercase hex: {value}"
    );
}

fn assert_manifest_identity_contract(
    rows: &[NativeSharedPrimitiveContractManifestRow],
    lines: &[String],
    text: &str,
    row_count: usize,
    digest: &ProofDigest,
    sha256: &str,
) {
    assert_eq!(row_count, rows.len(), "row count helper must match rows");
    assert_eq!(
        lines.len(),
        rows.len(),
        "line helper must preserve one line per row"
    );
    assert_eq!(
        lines,
        &rows
            .iter()
            .map(NativeSharedPrimitiveContractManifestRow::to_key_value_line)
            .collect::<Vec<_>>(),
        "line helper must be the row-owned escaped key/value form"
    );
    assert_eq!(
        text,
        format!("{}\n", lines.join("\n")),
        "text helper must be the canonical newline-terminated line stream"
    );
    assert_eq!(
        sha256,
        digest.to_string(),
        "SHA helper must expose the typed digest without consumer recomputation"
    );
    assert_sha256_shape(sha256);
    for line in lines {
        assert!(
            !line.contains('\n') && !line.contains('\r') && !line.contains('\t'),
            "manifest helper emitted raw control whitespace: {line:?}"
        );
    }
}

fn manifest_lines_contain_key(lines: &[String], key: &str) -> bool {
    let prefix = format!("{key}=");
    lines.iter().any(|line| line.starts_with(&prefix))
}

fn manifest_line_value<'a>(lines: &'a [String], key: &str) -> Option<&'a str> {
    let prefix = format!("{key}=");
    lines.iter().find_map(|line| line.strip_prefix(&prefix))
}

fn assert_operation_manifest_rows_cover(
    lines: &[String],
    contract_prefix: &str,
    operations: &[&str],
) {
    for operation in operations {
        let operation_prefix = format!("{contract_prefix}.operation.{operation}");
        let status = manifest_line_value(lines, &format!("{operation_prefix}.status"))
            .unwrap_or_else(|| panic!("{contract_prefix} must publish status for {operation}"));
        let fail_closed = manifest_line_value(lines, &format!("{operation_prefix}.fail_closed"))
            .unwrap_or_else(|| {
                panic!("{contract_prefix} must publish fail_closed for {operation}")
            });
        match status {
            "available" => {
                assert_eq!(
                    fail_closed, "false",
                    "{contract_prefix} available row {operation} must not fail closed"
                );
                assert!(
                    manifest_lines_contain_key(lines, &format!("{operation_prefix}.feature_guard")),
                    "{contract_prefix} must publish a feature guard row for {operation}"
                );
                assert!(
                    manifest_lines_contain_key(
                        lines,
                        &format!("{operation_prefix}.native_instructions")
                    ) || manifest_lines_contain_key(
                        lines,
                        &format!("{operation_prefix}.native_instruction"),
                    ),
                    "{contract_prefix} must publish native instruction coverage for {operation}"
                );
                assert!(
                    manifest_lines_contain_key(lines, &format!("{operation_prefix}.semantics")),
                    "{contract_prefix} must publish semantics for {operation}"
                );
            }
            "deferred" | "unavailable" => {
                assert_eq!(
                    fail_closed, "true",
                    "{contract_prefix} unavailable row {operation} must fail closed"
                );
                assert!(
                    manifest_lines_contain_key(lines, &format!("{operation_prefix}.reason")),
                    "{contract_prefix} unavailable row {operation} must publish a reason"
                );
                assert_eq!(
                    manifest_line_value(lines, &format!("{operation_prefix}.consumer_policy")),
                    Some(CHC_X86_UNSIGNED_VECTOR_COMPARE_FAIL_CLOSED_POLICY),
                    "{contract_prefix} unavailable row {operation} must reject lowering"
                );
                assert!(
                    !manifest_lines_contain_key(
                        lines,
                        &format!("{operation_prefix}.feature_guard")
                    ),
                    "{contract_prefix} unavailable row {operation} must not publish a feature guard"
                );
                assert!(
                    !manifest_lines_contain_key(
                        lines,
                        &format!("{operation_prefix}.native_instructions")
                    ) && !manifest_lines_contain_key(
                        lines,
                        &format!("{operation_prefix}.native_instruction")
                    ),
                    "{contract_prefix} unavailable row {operation} must not publish native instruction coverage"
                );
                assert!(
                    !manifest_lines_contain_key(lines, &format!("{operation_prefix}.semantics")),
                    "{contract_prefix} unavailable row {operation} must not publish semantics"
                );
            }
            other => panic!("{contract_prefix} operation {operation} has unknown status {other}"),
        }
    }
}

#[test]
fn producer_owned_manifest_identity_helpers_are_public_and_self_consistent() {
    let petri_rows = petri_successor_trust_mc_chc_shared_primitive_contract_manifest_rows();
    let petri_lines =
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_lines();
    let petri_text =
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_key_value_text();
    let petri_digest = petri_successor_trust_mc_chc_shared_primitive_contract_manifest_digest();
    let petri_sha256 = petri_successor_trust_mc_chc_shared_primitive_contract_manifest_sha256();
    assert_manifest_identity_contract(
        &petri_rows,
        &petri_lines,
        &petri_text,
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_row_count(),
        &petri_digest,
        &petri_sha256,
    );
    assert_eq!(
        petri_successor_trust_mc_chc_shared_primitive_contract_manifest_row_count(),
        46,
        "Petri/TrustMc contract row count is part of the downstream MCC contract"
    );
    assert!(petri_lines.contains(&"production.solver_evidence.owner_suite=ay".to_string()));
    assert!(petri_lines.contains(&"production.requires_emitted_solver_artifacts=true".to_string()));

    let hardware_rows = chc_x86_hardware_vector_contract_manifest_rows();
    let hardware_lines = chc_x86_hardware_vector_contract_manifest_key_value_lines();
    let hardware_text = chc_x86_hardware_vector_contract_manifest_key_value_text();
    let hardware_digest = chc_x86_hardware_vector_contract_manifest_digest();
    let hardware_sha256 = chc_x86_hardware_vector_contract_manifest_sha256();
    assert_manifest_identity_contract(
        &hardware_rows,
        &hardware_lines,
        &hardware_text,
        chc_x86_hardware_vector_contract_manifest_row_count(),
        &hardware_digest,
        &hardware_sha256,
    );
    assert!(hardware_lines.contains(&"hardware_vector_contract_set.contract_count=4".to_string()));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.binop.mul.native_instruction=pmulld"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.pack_lanes.native_instructions=movd_to_xmm;punpckldq;punpcklqdq;pshufd_same_lane_broadcast"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.pack_lanes.native_instructions=movq_to_xmm;punpcklqdq;pshufd_same_lane_broadcast"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.binop.add.native_instructions=paddd"
            .to_string()
    ));
    assert!(
        hardware_lines.contains(
            &"hardware_vector_contract_set.contract.0.operation.binop.shl.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.binop.lshr.native_instructions=movd_from_xmm;pshufd;mov_to_ecx;shl_rr_or_shr_rr_or_sar_rr;movd_to_xmm;punpckldq;punpcklqdq"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.binop.ashr.composition=lane_count_4;each_rhs_lane_in_0_31;x86_shift_count_masking_not_source_semantics"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.binop.add.native_instructions=paddq"
            .to_string()
    ));
    assert!(
        hardware_lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.eq.feature_guard=x86.sse4.1"
                .to_string()
        )
    );
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.icmp.eq.native_instructions=pcmpeqq"
            .to_string()
    ));
    assert!(
        hardware_lines.contains(
            &"hardware_vector_contract_set.contract.1.operation.icmp.slt.feature_guard=x86.sse4.2"
                .to_string()
        )
    );
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.icmp.slt.composition=pcmpgtq(rhs,lhs)"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.0.operation.insert_element.feature_guard=x86.sse2"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.insert_element.native_instructions=movq_to_xmm;pshufd;punpcklqdq;pxor_zero_base"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.1.operation.extract_element.native_instructions=pshufd;movq_from_xmm"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.1.trust_cg_x86_vector.host_jit_feature_guard=runtime_detected_optional_x86.sse4.1+x86.sse4.2"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.2.contract.name=chc_x86.v16_i8".to_string()
    ));
    assert!(
        hardware_lines.contains(
            &"hardware_vector_contract_set.contract.2.operation.icmp.eq.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.2.operation.icmp.eq.native_instructions=pcmpeqb"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.2.operation.icmp.slt.composition=pcmpgtb(rhs,lhs)"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &format!(
            "hardware_vector_contract_set.contract.2.operation.vector.mask_to_bits.semantics={CHC_X86_V16_I8_MASK_TO_BITS_SEMANTICS}"
        )
    ));
    assert!(hardware_lines.contains(
        &format!(
            "hardware_vector_contract_set.contract.2.operation.vector.mask_to_bits.composition={CHC_X86_V16_I8_MASK_TO_BITS_COMPOSITION}"
        )
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.3.contract.name=chc_x86.v8_i16".to_string()
    ));
    assert!(
        hardware_lines.contains(
            &"hardware_vector_contract_set.contract.3.operation.icmp.eq.feature_guard=x86.sse2"
                .to_string()
        )
    );
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.3.operation.icmp.eq.native_instructions=pcmpeqw"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.3.operation.icmp.slt.composition=pcmpgtw(rhs,lhs)"
            .to_string()
    ));
    assert!(hardware_lines.contains(
        &format!(
            "hardware_vector_contract_set.contract.3.operation.vector.mask_to_bits.semantics={CHC_X86_V8_I16_MASK_TO_BITS_SEMANTICS}"
        )
    ));
    assert!(hardware_lines.contains(
        &format!(
            "hardware_vector_contract_set.contract.3.operation.vector.mask_to_bits.composition={CHC_X86_V8_I16_MASK_TO_BITS_COMPOSITION}"
        )
    ));
    // The x86-64 vector-compare per-cell rule (`docs/dialects.md`): the
    // unsigned compares are available on every descriptor, `v16_i8` (contract
    // index 2) included since 2026-09-28, each on the SSE2 sign-bit bias.
    let contract_names: Vec<&str> = (0..)
        .map_while(|index| {
            manifest_line_value(
                &hardware_lines,
                &format!("hardware_vector_contract_set.contract.{index}.contract.name"),
            )
        })
        .collect();
    assert!(contract_names.contains(&"chc_x86.v16_i8"));
    for (contract_index, contract_name) in contract_names.iter().enumerate() {
        for unsigned_operation in ["icmp.ult", "icmp.ule", "icmp.ugt", "icmp.uge"] {
            let operation_prefix = format!(
                "hardware_vector_contract_set.contract.{contract_index}.operation.{unsigned_operation}"
            );
            let value = |suffix: &str| {
                manifest_line_value(&hardware_lines, &format!("{operation_prefix}.{suffix}"))
            };
            assert_eq!(
                value("status"),
                Some("available"),
                "{contract_name}: {operation_prefix}"
            );
            assert_eq!(value("reason"), Some("canonical_contract"));
            assert_eq!(value("fail_closed"), Some("false"), "{operation_prefix}");
            assert_eq!(value("consumer_policy"), None, "{operation_prefix}");
            assert_eq!(
                value("feature_guard"),
                Some("x86.sse2"),
                "{contract_name}: the sign-bit bias composition is SSE2 ({operation_prefix})"
            );
            assert!(
                value("composition").is_some_and(|c| c.contains("sign_bit_bias")),
                "{operation_prefix} must publish its bias composition"
            );
        }
    }
    assert!(hardware_lines.contains(
        &"hardware_vector_contract_set.contract.2.operation.icmp.ult.composition=pcmpgtb(pxor(rhs,sign_bit_bias),pxor(lhs,sign_bit_bias));sign_bit_bias:splat_i8(0x80)"
            .to_string()
    ));

    let aggregate_rows = ty_shared_primitive_manifest_rows();
    let aggregate_lines = ty_shared_primitive_manifest_key_value_lines();
    let aggregate_text = ty_shared_primitive_manifest_key_value_text();
    let aggregate_digest = ty_shared_primitive_manifest_digest();
    let aggregate_sha256 = ty_shared_primitive_manifest_sha256();
    assert_manifest_identity_contract(
        &aggregate_rows,
        &aggregate_lines,
        &aggregate_text,
        ty_shared_primitive_manifest_row_count(),
        &aggregate_digest,
        &aggregate_sha256,
    );
    assert!(
        aggregate_lines.contains(&"ty_shared_primitive_manifest.component_count=3".to_string())
    );
    assert!(aggregate_lines.contains(
        &"ty_shared_primitive_manifest.component.2.rows_api=chc_x86_hardware_vector_contract_manifest_rows()".to_string()
    ));

    assert_ne!(
        petri_sha256, hardware_sha256,
        "distinct producer manifests must have distinct identities"
    );
    assert_ne!(
        petri_sha256, aggregate_sha256,
        "aggregate identity must not alias the Petri/TrustMc contract identity"
    );
    assert_ne!(
        hardware_sha256, aggregate_sha256,
        "aggregate identity must not alias the hardware contract-set identity"
    );
}

#[test]
fn hardware_vector_manifest_rows_cover_every_listed_operation() {
    let rows = chc_x86_hardware_vector_contract_manifest_rows();
    let lines = chc_x86_hardware_vector_contract_manifest_key_value_lines();
    let keys = rows
        .iter()
        .map(|row| row.key.as_str())
        .collect::<BTreeSet<_>>();

    assert_eq!(
        keys.len(),
        rows.len(),
        "hardware vector manifest keys must stay unique for key/value consumers"
    );
    assert_operation_manifest_rows_cover(
        &lines,
        "hardware_vector_contract_set.contract.0",
        CHC_X86_V4_I32_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    );
    assert_operation_manifest_rows_cover(
        &lines,
        "hardware_vector_contract_set.contract.1",
        CHC_X86_V2_I64_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    );
    assert_operation_manifest_rows_cover(
        &lines,
        "hardware_vector_contract_set.contract.2",
        CHC_X86_V16_I8_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    );
    assert_operation_manifest_rows_cover(
        &lines,
        "hardware_vector_contract_set.contract.3",
        CHC_X86_V8_I16_HARDWARE_VECTOR_CONTRACT_OPERATIONS,
    );
}

#[test]
fn aggregate_manifest_embeds_hardware_rows_for_consumer_replay() {
    let aggregate_rows = ty_shared_primitive_manifest_rows();
    let values: BTreeMap<_, _> = aggregate_rows
        .iter()
        .map(|row| (row.key.as_str(), row.value.as_str()))
        .collect();
    let hardware_rows = chc_x86_hardware_vector_contract_manifest_rows();
    let embedded_count = values
        .get("ty_shared_primitive_manifest.hardware_vector_contract_row_count")
        .and_then(|value| value.parse::<usize>().ok())
        .expect("aggregate manifest must expose embedded hardware row count");

    assert_eq!(
        embedded_count,
        chc_x86_hardware_vector_contract_manifest_row_count()
    );
    assert_eq!(embedded_count, hardware_rows.len());
    for (index, hardware_row) in hardware_rows.iter().enumerate() {
        let key_field =
            format!("ty_shared_primitive_manifest.hardware_vector_contract_row.{index}.key");
        let value_field =
            format!("ty_shared_primitive_manifest.hardware_vector_contract_row.{index}.value");
        assert_eq!(
            values.get(key_field.as_str()).copied(),
            Some(hardware_row.key.as_str()),
            "aggregate manifest must preserve embedded hardware row key {index}"
        );
        assert_eq!(
            values.get(value_field.as_str()).copied(),
            Some(hardware_row.value.as_str()),
            "aggregate manifest must preserve embedded hardware row value {index}"
        );
    }
}
