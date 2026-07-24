// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::super::tests_contract_gate_support::{
    mk_bool_backend_and_mapping, mk_qf_lia_backend_and_mapping, mk_qf_uf_backend_and_mapping,
    neg_false,
};
use super::support::{
    classify_candidate, evaluate_gate_case, print_and_verify_gate_matrix, ReplacementGateRow,
};

#[test]
fn test_2386_proof_replacement_gate_snapshot_prints_status_matrix() {
    let mut rows: Vec<ReplacementGateRow> = Vec::new();

    {
        let (mut backend, map, _, _) = mk_bool_backend_and_mapping();
        let (proof_present, native_quality_complete, unlimited, zero_trust) =
            evaluate_gate_case(&mut backend, &map, &neg_false());
        rows.push(ReplacementGateRow {
            case: "QF_BOOL",
            proof_present,
            native_quality_complete,
            unlimited: classify_candidate(&unlimited),
            zero_trust: classify_candidate(&zero_trust),
        });
    }

    {
        let (mut backend, map, _, _) = mk_qf_uf_backend_and_mapping();
        let (proof_present, native_quality_complete, unlimited, zero_trust) =
            evaluate_gate_case(&mut backend, &map, &neg_false());
        rows.push(ReplacementGateRow {
            case: "QF_UF",
            proof_present,
            native_quality_complete,
            unlimited: classify_candidate(&unlimited),
            zero_trust: classify_candidate(&zero_trust),
        });
    }

    {
        let (mut backend, map, _, _, _) = mk_qf_lia_backend_and_mapping();
        let (proof_present, native_quality_complete, unlimited, zero_trust) =
            evaluate_gate_case(&mut backend, &map, &neg_false());
        rows.push(ReplacementGateRow {
            case: "QF_LIA",
            proof_present,
            native_quality_complete,
            unlimited: classify_candidate(&unlimited),
            zero_trust: classify_candidate(&zero_trust),
        });
    }

    print_and_verify_gate_matrix(&rows);
}
