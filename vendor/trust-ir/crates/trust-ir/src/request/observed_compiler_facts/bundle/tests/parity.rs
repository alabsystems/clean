// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn module_obligation_duplicates_are_not_silently_collapsed_by_the_known_id_index() {
    let mut bundle = fixture();
    let mut duplicate = bundle.module.proof_obligations[0].clone();
    duplicate.formula = Some(crate::ProofFormula::smtlib2("false", "Bool"));
    let id = duplicate.id;
    bundle
        .module
        .proof_obligations
        .extend([duplicate.clone(), duplicate]);
    let errors = parity(&bundle);
    assert_eq!(
        &errors[..2],
        &[
            E::DuplicateModuleObligationId(id),
            E::DuplicateModuleObligationId(id)
        ]
    );
}

#[test]
fn whole_compiler_fact_constituent_matches_original_with_every_primitive_family() {
    assert!(parity(&fixture()).is_empty());
    let mut empty = fixture();
    empty.compiler_facts = Default::default();
    assert!(
        parity(&empty)
            .iter()
            .any(|error| matches!(error, E::MissingObligationSource { .. }))
    );
}

#[test]
fn duplicate_ids_are_per_family_and_replacing_maps_drive_later_bindings() {
    for family in 0..6 {
        let mut bundle = fixture();
        match family {
            0 => bundle
                .compiler_facts
                .adt_layouts
                .push(bundle.compiler_facts.adt_layouts[0].clone()),
            1 => bundle
                .compiler_facts
                .fat_pointers
                .push(bundle.compiler_facts.fat_pointers[0].clone()),
            2 => {
                let mut row = bundle.compiler_facts.trait_object_metadata[0].clone();
                row.trait_id = 11;
                row.function = Some(FuncId::new(99));
                bundle.compiler_facts.trait_object_metadata.push(row);
            }
            3 => {
                let mut row = bundle.compiler_facts.pointer_offsets[0].clone();
                row.function = FuncId::new(99);
                bundle.compiler_facts.pointer_offsets.push(row);
            }
            4 => {
                let mut row = bundle.compiler_facts.casts[0].clone();
                row.function = FuncId::new(99);
                bundle.compiler_facts.casts.push(row);
            }
            _ => {
                let mut row = bundle.compiler_facts.monomorphizations[0].clone();
                row.function = Some(FuncId::new(99));
                bundle.compiler_facts.monomorphizations.push(row);
            }
        }
        assert!(!parity(&bundle).is_empty());
    }
}

#[test]
fn monomorphization_text_digest_function_and_generic_argument_checks_keep_order() {
    for change in 0..10 {
        let mut bundle = fixture();
        let row = &mut bundle.compiler_facts.monomorphizations[0];
        match change {
            0 => row.source_item = " \u{2003}".into(),
            1 => row.symbol = "bad\u{7f}symbol".into(),
            2 => row.source_item = "\u{3bb}".repeat(3000),
            3 => {
                row.stable_digest = ProofDigest {
                    algorithm: ProofDigestAlgorithm::TrustIrStableV1,
                    bytes: [0; 32],
                }
            }
            4 => row.function = Some(FuncId::new(99)),
            5 => {
                row.generic_args = vec![NativeGenericArg::Ty(Ty::Tuple(vec![Ty::PtrConst(
                    Box::new(Ty::Error),
                )]))]
            }
            6 => {
                row.generic_args = vec![NativeGenericArg::Const {
                    ty: Ty::Vector(Box::new(Ty::Bool), 2),
                    value: Constant::Vector(vec![Constant::Bool(true), Constant::Int(1)]),
                }]
            }
            7 => {
                row.generic_args = vec![
                    NativeGenericArg::LifetimeErased,
                    NativeGenericArg::Placeholder { index: 99 },
                ]
            }
            8 => {
                bundle.module.target_info.as_mut().unwrap().pointer_size = 4;
                row.generic_args = vec![NativeGenericArg::Const {
                    ty: Ty::Usize,
                    value: Constant::Int(1i128 << 32),
                }];
            }
            _ => {
                let mut second = row.clone();
                second.id = NativeMonomorphizationId::new(1);
                bundle.compiler_facts.monomorphizations.push(second);
            }
        }
        parity(&bundle);
    }
}

#[test]
fn duplicate_public_ids_replace_the_previous_value_while_embedded_join_uses_first_source() {
    let mut bundle = fixture();
    let public = bundle.compiler_facts.obligation_sources[0]
        .public_obligation_id
        .clone();
    bundle.compiler_facts.obligation_sources[1].public_obligation_id = public.clone();
    let mut third = bundle.compiler_facts.obligation_sources[0].clone();
    third.obligation = ProofId::new(2);
    bundle.compiler_facts.obligation_sources.push(third);
    let errors = parity(&bundle);
    let previous: Vec<_> = errors
        .iter()
        .filter_map(|error| {
            if let E::DuplicatePublicObligationSource {
                first_obligation,
                duplicate_obligation,
                ..
            } = error
            {
                Some((*first_obligation, *duplicate_obligation))
            } else {
                None
            }
        })
        .collect();
    assert_eq!(
        previous,
        vec![
            (ProofId::new(0), ProofId::new(1)),
            (ProofId::new(1), ProofId::new(2))
        ]
    );
    let mut later = bundle.compiler_facts.obligation_sources[0].clone();
    later.public_obligation_id = "later".into();
    later.span.as_mut().unwrap().line = 999;
    bundle.compiler_facts.obligation_sources.push(later);
    let errors = parity(&bundle);
    assert!(!errors.iter().any(|error| matches!(error, E::EmbeddedObligationSourceSpanMismatch { obligation, .. } if *obligation == ProofId::new(0))));
    assert!(!errors.iter().any(|error| matches!(error, E::EmbeddedPublicObligationIdMismatch { obligation, .. } if *obligation == ProofId::new(0))));
}

#[test]
fn source_unknown_duplicate_function_monomorphization_and_sorted_fact_checks_match() {
    for change in 0..10 {
        let mut bundle = fixture();
        let source = &mut bundle.compiler_facts.obligation_sources[0];
        match change {
            0 => source.obligation = ProofId::new(99),
            1 => source.public_obligation_id = "bad?identity".into(),
            2 => source.function = Some(FuncId::new(99)),
            3 => source.monomorphization = Some(NativeMonomorphizationId::new(99)),
            4 => source.facts.push(source.facts[0]),
            5 => source.facts.clear(),
            6 => {
                source.monomorphization = None;
                source.facts.extend([
                    NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(3)),
                    NativeCompilerFactRef::Monomorphization(NativeMonomorphizationId::new(1)),
                ]);
            }
            7 => source.facts.push(NativeCompilerFactRef::Monomorphization(
                NativeMonomorphizationId::new(2),
            )),
            8 => source
                .facts
                .push(NativeCompilerFactRef::AdtLayout(NativeCompilerFactId::new(
                    99,
                ))),
            _ => {
                let source = source.clone();
                bundle.compiler_facts.obligation_sources.push(source);
            }
        }
        parity(&bundle);
    }
}

#[test]
fn bound_cast_pointer_function_and_obligation_correspondence_preserves_original_guards() {
    for change in 0..9 {
        let mut bundle = fixture();
        let source = &mut bundle.compiler_facts.obligation_sources[0];
        match change {
            0 => {
                source.cause = NativeObligationCause::CastCheck;
                source.facts.clear();
            }
            1 => {
                source.cause = NativeObligationCause::PointerOffset;
                source.facts.clear();
            }
            2 => source.function = None,
            3 => bundle.compiler_facts.casts[0].obligations.clear(),
            4 => bundle.compiler_facts.pointer_offsets[0].obligations.clear(),
            5 => bundle.compiler_facts.trait_object_metadata[0]
                .obligations
                .clear(),
            6 => {
                bundle.compiler_facts.pointer_offsets[0].provenance =
                    NativePointerOffsetProvenance::Unsupported(NativeUnsupportedMode::new(
                        NativeUnsupportedModeReason::Other,
                        "not representable",
                    ))
            }
            7 => {
                source.cause = NativeObligationCause::CastCheck;
                bundle.compiler_facts.casts[0].function = FuncId::new(99);
            }
            _ => {
                source.cause = NativeObligationCause::PointerOffset;
                bundle.compiler_facts.pointer_offsets[0].function = FuncId::new(99);
            }
        }
        parity(&bundle);
    }
}

#[test]
fn metadata_source_coverage_requires_matching_type_and_exact_vtable_identity() {
    for change in 0..5 {
        let mut bundle = fixture();
        match change {
            0 => bundle.compiler_facts.obligation_sources[0]
                .facts
                .retain(|fact| !matches!(fact, NativeCompilerFactRef::TraitObjectMetadata(_))),
            1 => bundle.compiler_facts.obligation_sources[0]
                .facts
                .retain(|fact| !matches!(fact, NativeCompilerFactRef::FatPointer(_))),
            2 => {
                bundle.compiler_facts.trait_object_metadata[0].ty =
                    Ty::Tuple(vec![Ty::Tuple(vec![Ty::U32])])
            }
            3 => {
                bundle.compiler_facts.fat_pointers[0].layout.metadata =
                    Some(crate::PointerMetadataShape::VTable { trait_id: 10 })
            }
            _ => bundle.compiler_facts.obligation_sources[0].facts.push(
                NativeCompilerFactRef::TraitObjectMetadata(NativeCompilerFactId::new(4)),
            ),
        }
        parity(&bundle);
    }
}

#[test]
fn embedded_first_proof_source_range_text_and_public_identity_guards_match() {
    for change in 0..14 {
        let mut bundle = fixture();
        let source = bundle.module.proof_obligations[0].source.as_mut().unwrap();
        match change {
            0 => bundle.module.proof_obligations[0].source = None,
            1 => source.source_id = " leading".into(),
            2 => source.assertion_id = "a\u{7f}".into(),
            3 => source.source_id = "\u{3bb}".repeat(513),
            4 => source.range.as_mut().unwrap().file = 99,
            5 => source.range.as_mut().unwrap().start_line = 0,
            6 => source.range.as_mut().unwrap().end_line = 1,
            7 => source.public = None,
            8 => source.public.as_mut().unwrap().obligation_id = "bad#id".into(),
            9 => {
                source.public.as_mut().unwrap().semantic_digest = ProofDigest {
                    algorithm: ProofDigestAlgorithm::TrustIrStableV1,
                    bytes: [0; 32],
                }
            }
            10 => source.public.as_mut().unwrap().obligation_id = "other".into(),
            11 => {
                bundle.compiler_facts.obligation_sources[0]
                    .span
                    .as_mut()
                    .unwrap()
                    .line = 50
            }
            12 => {
                let mut duplicate = bundle.module.proof_obligations[0].clone();
                duplicate.source = None;
                bundle.module.proof_obligations.insert(0, duplicate);
            }
            _ => {
                bundle
                    .module
                    .proof_obligations
                    .retain(|row| row.id != ProofId::new(0));
            }
        }
        parity(&bundle);
    }
}

#[test]
fn observed_identity_text_matches_actual_original_rules_at_unicode_and_byte_boundaries() {
    for value in [
        "".into(),
        "a".into(),
        "a b".into(),
        " x".into(),
        "x\u{2003}".into(),
        "x\0y".into(),
        "\u{200b}".into(),
        "\u{3bb}".repeat(512),
        "\u{3bb}".repeat(513),
        "p?x".into(),
        "x#y".into(),
    ] {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            text::identity(&value, true, &mut session, site()).unwrap(),
            crate::proof::is_valid_proof_obligation_source_text_id(&value)
        );
        assert_eq!(
            text::public_id(&value, &mut session, site()).unwrap(),
            crate::proof::is_canonical_public_obligation_id(&value)
        );
        assert_eq!(
            text::identity(&value, false, &mut session, site()).unwrap(),
            !value.is_empty() && value.trim() == value && !value.chars().any(char::is_control)
        );
    }
}

#[test]
fn generic_inline_error_and_target_width_constant_walks_match_actual_original_helpers() {
    let types = vec![
        Ty::U32,
        Ty::Tuple(vec![Ty::U32, Ty::PtrConst(Box::new(Ty::Error))]),
        Ty::Vector(Box::new(Ty::Error), 0),
        Ty::Tensor(Box::new(Ty::Error), 2),
        Ty::Tensor(Box::new(Ty::U32), 0),
        Ty::Struct(StructId::new(99)),
        Ty::Refine(crate::TyId::new(0), crate::PredId::new(0)),
    ];
    for ty in &types {
        let mut observer = Observer::default();
        let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
        assert_eq!(
            types::contains_error(ty, &mut session, site()).unwrap(),
            ty.contains_error()
        );
    }
    let constants = vec![
        (Constant::Int(1i128 << 32), Ty::Usize),
        (Constant::Int(-1), Ty::U32),
        (Constant::Int(0xd800), Ty::Char),
        (Constant::U128(0), Ty::U128),
        (
            Constant::Vector(vec![Constant::Int(3), Constant::Int(300)]),
            Ty::Vector(Box::new(Ty::U8), 2),
        ),
        (Constant::Vector(vec![]), Ty::Vector(Box::new(Ty::Error), 0)),
        (
            Constant::Aggregate(vec![Constant::Int(0), Constant::Int(0)]),
            Ty::FatPtr(crate::FatPtrKind::Str),
        ),
        (
            Constant::Bytes {
                data: vec![0; 3],
                utf8: false,
            },
            Ty::Array(crate::TyId::new(0), 3),
        ),
        (
            Constant::Splat {
                elem: Box::new(Constant::Uninit),
                len: 3,
            },
            Ty::Array(crate::TyId::new(0), 3),
        ),
    ];
    for bits in [0, 8, 32, 64, 128, 129] {
        for (value, ty) in &constants {
            let mut observer = Observer::default();
            let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
            assert_eq!(
                types::constant_matches(value, ty, bits, &mut session, site()).unwrap(),
                value.value_matches_ty(ty, bits)
            );
        }
    }
}
