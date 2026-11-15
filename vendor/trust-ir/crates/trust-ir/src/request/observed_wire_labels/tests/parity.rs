// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
#[test]
fn node_location_uses_complete_raw_sparse_function_name_and_unsigned_ordinals() {
    let m = module();
    let (e, _, _) = mapped(&m, &node(900));
    assert_eq!(
        e,
        E::TrustIrModuleHasNoWireIdentity {
            location: format!("function 'raw 'λ\0尾\n' bb{} #{}", u32::MAX, usize::MAX),
            construct: "raw construct"
        }
    );
}
#[test]
fn absent_actual_function_keeps_question_mark_not_forged_or_empty_name() {
    let m = module();
    assert!(
        matches!(mapped(&m,&node(999)).0,E::TrustIrModuleHasNoWireIdentity{location,..}if location.starts_with("function '?' bb"))
    );
}
#[test]
fn correct_indexed_duplicate_wins_over_earlier_physical_matching_id() {
    let mut m = Module::new("");
    m.functions = vec![
        function(2, "early"),
        function(99, "wrong slot"),
        function(2, "indexed"),
    ];
    let (e, _, _) = mapped(&m, &node(2));
    assert!(
        matches!(e,E::TrustIrModuleHasNoWireIdentity{location,..}if location.starts_with("function 'indexed'"))
    );
}
#[test]
fn wrong_indexed_id_triggers_first_physical_matching_fallback() {
    let mut m = Module::new("");
    m.functions = vec![
        function(2, "FIRST"),
        function(2, "later"),
        function(8, "wrong index"),
    ];
    let (e, _, _) = mapped(&m, &node(2));
    assert!(
        matches!(e,E::TrustIrModuleHasNoWireIdentity{location,..}if location.starts_with("function 'FIRST'"))
    );
}
#[test]
fn scope_location_preserves_full_u32_and_original_function_lookup() {
    let m = module();
    let row = BinaryProjectionError::InlinedScopeChainUnencodable {
        function: 900,
        scope: u32::MAX,
    };
    let (e, _, _) = mapped(&m, &row);
    assert_eq!(
        e,
        E::TrustIrModuleHasNoWireIdentity {
            location: format!("function 'raw 'λ\0尾\n' lexical scope #{}", u32::MAX),
            construct: "ScopeData.inlined_at"
        }
    );
}
#[test]
fn signature_location_uses_full_usize_and_not_unread_abi_detail() {
    let m = module();
    let row = BinaryProjectionError::SignatureAbiUnencodable {
        signature: usize::MAX,
        detail: "opaque λ\0".repeat(1000),
    };
    let (e, large, _) = mapped(&m, &row);
    assert_eq!(
        e,
        E::TrustIrModuleHasNoWireIdentity {
            location: format!("signature #{}", usize::MAX),
            construct: "FuncTy.abi (a typed signature ABI past its encoding limits)"
        }
    );
    let row = BinaryProjectionError::SignatureAbiUnencodable {
        signature: usize::MAX,
        detail: String::new(),
    };
    assert_eq!(large.events, mapped(&m, &row).1.events);
}
#[test]
fn count_location_keeps_full_u64_and_actual_static_raw_field() {
    let m = module();
    let row = BinaryProjectionError::CountExceedsFormat {
        what: "raw λ\0 field",
        count: u64::MAX,
    };
    assert_eq!(
        mapped(&m, &row).0,
        E::TrustIrModuleHasNoWireIdentity {
            location: format!("raw λ\0 field ({} entries)", u64::MAX),
            construct: "a count past the binary format's u32 limit"
        }
    );
}
#[test]
fn fixed_module_constructs_and_unsited_no_tag_match_actual_original_mapping() {
    let m = module();
    for row in [
        BinaryProjectionError::ConstructAheadOfWireTag {
            construct: "raw literal",
            site: None,
        },
        BinaryProjectionError::CompletenessClaimUnencodable,
        BinaryProjectionError::ProducerInternalType,
    ] {
        mapped(&m, &row);
    }
}
#[test]
fn original_projection_only_fallback_is_a_raw_module_diagnostic_not_acceptance() {
    let m = module();
    for row in [
        BinaryProjectionError::SignatureAbiRequiresCurrentFormat,
        BinaryProjectionError::DuplicateOmission(crate::ProofId::new(u32::MAX)),
        BinaryProjectionError::RetainedReference {
            obligation: crate::ProofId::new(1),
            location: "raw",
        },
    ] {
        assert_eq!(
            mapped(&m, &row).0,
            E::TrustIrModuleHasNoWireIdentity {
                location: "module".into(),
                construct: "a construct the binary writer refuses"
            }
        );
    }
}
#[test]
fn complete_actual_module_child_maps_every_rank_in_original_order() {
    let b = actual();
    let (rows, _, _) = observed(&b);
    assert_eq!(rows.len(), 2);
    assert!(matches!(
        &rows[0],
        E::TrustIrModuleHasNoWireIdentity {
            construct: "Module.completeness",
            ..
        }
    ));
    assert!(matches!(
        &rows[1],
        E::TrustIrModuleHasNoWireIdentity {
            construct: "Ty::Error (producer-internal)",
            ..
        }
    ));
}
#[test]
fn actual_encodable_module_empty_diagnostics_still_carries_no_identity_authority() {
    let mut b = actual();
    b.module = Module::new("encodable");
    assert!(observed(&b).0.is_empty());
}
#[test]
fn all_owned_long_raw_location_text_outlives_its_whole_source() {
    let mut m = module();
    m.functions[0].name = "raw 'λ\0尾\n".repeat(1700);
    let row = node(900);
    let expected = ordinary(&m, &row);
    let (e, _, _) = mapped(&m, &row);
    drop(m);
    assert_eq!(e, expected);
}
