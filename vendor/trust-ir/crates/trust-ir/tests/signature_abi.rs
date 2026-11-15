// Author: Andrew Yates | Copyright 2026 Andrew Yates | Apache-2.0
#![cfg(all(feature = "parser", feature = "binary", feature = "serde"))]
#[path = "../../trust-ir-conformance/tests/generate/signature_abi.rs"]
mod fixture;
use trust_ir::binary::{deserialize_module, serialize_module};
use trust_ir::signature_abi::*;

#[test]
fn derived_abi_view_checks_canonical_facts_before_exposing_placement() {
    let mut module = fixture::module().expect("signature_abi::module: test fixture");
    let mut function = trust_ir::Function::new(
        trust_ir::FuncId::new(0),
        "callee",
        trust_ir::FuncTyId::new(0),
        trust_ir::BlockId::new(0),
    );
    function.attrs.params = vec![trust_ir::ParamAttrs::default(); 6];
    function.attrs.params[0].sret = true;
    function.attrs.params[1].ext = trust_ir::ArgExt::SignExt;
    module.functions.push(function);
    let function = &module.functions[0];
    let view = function.fn_abi(&module).unwrap().unwrap();
    assert_eq!(view.is_vararg(), module.func_types[0].is_vararg);
    assert_eq!(view.calling_convention(), function.calling_conv);
    assert_eq!(view.placement(), module.func_types[0].abi.as_ref().unwrap());

    let mut wrong_vararg = module.clone();
    wrong_vararg.func_types[0].is_vararg = !wrong_vararg.func_types[0].is_vararg;
    assert!(wrong_vararg.functions[0].fn_abi(&wrong_vararg).is_err());

    let mut wrong_convention = module.clone();
    wrong_convention.functions[0].calling_conv = trust_ir::CallingConv::Fast;
    assert!(
        wrong_convention.functions[0]
            .fn_abi(&wrong_convention)
            .is_err()
    );

    let mut wrong_target = module.clone();
    wrong_target.target_info.as_mut().unwrap().pointer_size = 4;
    assert!(wrong_target.functions[0].fn_abi(&wrong_target).is_err());

    let mut legacy = module.clone();
    legacy.func_types[0].abi = None;
    assert!(legacy.functions[0].fn_abi(&legacy).unwrap().is_none());
}

#[test]
fn level_mapping_preserves_exact_abi_evidence() {
    let signature = fixture::signature();
    let mut identity = |ty: &trust_ir::Ty| Ok::<_, std::convert::Infallible>(ty.clone());
    assert_eq!(signature.try_map_level(&mut identity).unwrap(), signature);
}

#[test]
fn metadata_bearing_indirect_cannot_forge_data_pointer_or_census() {
    let mut placement = fixture::descriptor();
    placement.fixed_count = 1;
    placement.arguments = vec![AbiArgument {
        size: 1,
        align: 1,
        mode: AbiPassMode::Indirect {
            attributes: AbiAttributes::default(),
            metadata_attributes: Some(AbiAttributes::default()),
            on_stack: false,
            caller_copy: true,
        },
        bindings: vec![AbiBinding {
            place: AbiBindingPlace::Parameter(0),
            source_offset: 0,
            source_bytes: 1,
            carrier_offset: 0,
            carrier_bytes: 1,
        }],
    }];
    placement.result = AbiArgument {
        size: 0,
        align: 1,
        mode: AbiPassMode::Ignore,
        bindings: vec![],
    };
    let signature = trust_ir::FuncTy {
        params: vec![trust_ir::Ty::U8],
        returns: vec![],
        is_vararg: false,
        abi: Some(placement),
    };
    let mut sized = signature.clone();
    sized.params[0] = trust_ir::Ty::Ptr;
    let sized_argument = &mut sized.abi.as_mut().unwrap().arguments[0];
    if let AbiPassMode::Indirect {
        metadata_attributes,
        ..
    } = &mut sized_argument.mode
    {
        *metadata_attributes = None;
    }
    sized_argument.bindings[0].carrier_bytes = 8;
    assert!(sized.abi.as_ref().unwrap().validate(&sized).is_ok());
    assert!(
        signature
            .abi
            .as_ref()
            .unwrap()
            .validate(&signature)
            .is_err()
    );
}

#[test]
fn canonical_attributes_must_agree_with_every_source_owner_of_a_carrier() {
    let mut module = fixture::module().expect("signature_abi::module: test fixture");
    let mut placement = fixture::descriptor();
    placement.fixed_count = 2;
    placement.result = AbiArgument {
        size: 0,
        align: 1,
        mode: AbiPassMode::Ignore,
        bindings: vec![],
    };
    placement.arguments = (0..2)
        .map(|offset| AbiArgument {
            size: 1,
            align: 1,
            mode: AbiPassMode::Direct(AbiScalar {
                register: AbiRegister {
                    class: AbiRegisterClass::Integer,
                    bytes: 1,
                },
                source_offset: 0,
                source_bytes: 1,
                value_bits: 8,
                attributes: AbiAttributes {
                    extension: AbiExtension::Sign,
                    ..Default::default()
                },
            }),
            bindings: vec![AbiBinding {
                place: AbiBindingPlace::Parameter(0),
                source_offset: 0,
                source_bytes: 1,
                carrier_offset: offset,
                carrier_bytes: 1,
            }],
        })
        .collect();
    module.func_types[0] = trust_ir::FuncTy {
        params: vec![trust_ir::Ty::I16],
        returns: vec![],
        is_vararg: false,
        abi: Some(placement),
    };
    let mut function = trust_ir::Function::new(
        trust_ir::FuncId::new(0),
        "packed",
        trust_ir::FuncTyId::new(0),
        trust_ir::BlockId::new(0),
    );
    function.attrs.params.push(trust_ir::ParamAttrs {
        ext: trust_ir::ArgExt::SignExt,
        ..Default::default()
    });
    module.functions.push(function);
    assert!(module.functions[0].fn_abi(&module).unwrap().is_some());
    if let AbiPassMode::Direct(scalar) =
        &mut module.func_types[0].abi.as_mut().unwrap().arguments[1].mode
    {
        scalar.attributes.extension = AbiExtension::Zero;
    }
    // The first owner still agrees. The second source owner must not be
    // hidden by a first-match lookup of the shared lowered parameter.
    assert!(module.functions[0].fn_abi(&module).is_err());
}

#[test]
fn signature_abi_wire_allocation_preserves_all_shipped_versions() {
    let bytes = serialize_module(&fixture::module().expect("signature_abi::module: test fixture"))
        .expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 60);
    assert_eq!(trust_ir::binary::SIGNATURE_ABI_FORMAT_VERSION, 60);
    assert_eq!(trust_ir::binary::ASSERT_KIND_FORMAT_VERSION, 52);
    assert_eq!(trust_ir::binary::CALL_UNWIND_BOUNDARY_FORMAT_VERSION, 53);
    assert_eq!(trust_ir::binary::EFFECT_SUMMARY_FORMAT_VERSION, 59);
    for stale_version in [38u32, 51, 52, 58, 59] {
        let mut wrong = bytes.clone();
        wrong[8..12].copy_from_slice(&stale_version.to_le_bytes());
        assert!(
            deserialize_module(&wrong).is_err(),
            "typed placement under v{stale_version}"
        );
    }
}

#[test]
fn complete_signature_roundtrips_and_retains_padded_hfa_and_hidden_result() {
    let module = fixture::module().expect("signature_abi::module: test fixture");
    let abi = module.func_types[0].abi.as_ref().unwrap();
    abi.validate(&module.func_types[0]).unwrap();
    assert_eq!(
        SignatureAbi::from_canonical_text(&abi.to_canonical_text()).unwrap(),
        *abi
    );
    assert_eq!(
        deserialize_module(&serialize_module(&module).expect("serialize_module: test fixture"))
            .unwrap(),
        module
    );
    assert_eq!(
        rmp_serde::from_slice::<trust_ir::Module>(&rmp_serde::to_vec(&module).unwrap()).unwrap(),
        module
    );
    assert_eq!(
        trust_ir::parser::parse_module(&module.to_string()).unwrap(),
        module
    );
    assert_eq!(
        serde_json::from_str::<trust_ir::Module>(&serde_json::to_string(&module).unwrap()).unwrap(),
        module
    );
}
#[test]
fn canonical_descriptor_rejects_duplicate_unknown_overflow_trailing_and_noncanonical_text() {
    let text = fixture::descriptor().to_canonical_text();
    let mutants = [
        text.replacen("{target=", "{unknown=", 1),
        text.replacen("fixed_count=5", "fixed_count=5,fixed_count=5", 1),
        text.replacen("fixed_count=5", "fixed_count=18446744073709551616", 1),
        text.replacen("fixed_count=5", "fixed_count=05", 1),
        format!("{text}x"),
        text.replacen("{target=", "{ target=", 1),
        text.replacen("\"sign\"", "\"unrecorded\"", 1),
    ];
    for mutant in mutants {
        assert!(
            SignatureAbi::from_canonical_text(&mutant).is_err(),
            "{mutant}"
        );
    }
    assert!(SignatureAbi::from_canonical_text(&" ".repeat(MAX_ABI_TEXT_BYTES + 1)).is_err());
    assert!(
        SignatureAbi::from_canonical_text(&format!("{}0{}", "[".repeat(100), "]".repeat(100)))
            .is_err()
    );
}
#[test]
fn ignored_and_flattened_census_cannot_drop_duplicate_or_reassign_carriers() {
    let signature = fixture::signature();
    let base = fixture::descriptor();
    let mut omitted = base.clone();
    omitted.arguments[2].bindings.pop();
    let mut duplicate = base.clone();
    duplicate.arguments[2].bindings[1].place = AbiBindingPlace::Parameter(2);
    let mut hidden = base.clone();
    hidden.result.bindings[0].place = AbiBindingPlace::Parameter(0);
    let mut nonpointer = signature.clone();
    nonpointer.params[0] = trust_ir::Ty::U64;
    let mut ignored = base.clone();
    ignored.arguments[0].bindings.push(AbiBinding {
        place: AbiBindingPlace::Parameter(6),
        source_offset: 0,
        source_bytes: 0,
        carrier_offset: 0,
        carrier_bytes: 0,
    });
    let mut padded = base.clone();
    if let AbiPassMode::Cast { rest, .. } = &mut padded.arguments[3].mode {
        rest.total = 20;
    }
    for mutant in [omitted, duplicate, hidden, ignored, padded] {
        assert!(mutant.validate(&signature).is_err());
    }
    assert!(base.validate(&nonpointer).is_err());
}
#[test]
fn source_extent_and_unsigned_overflow_are_refused() {
    let signature = fixture::signature();
    let mut abi = fixture::descriptor();
    abi.arguments[4].bindings[0].source_bytes = 8;
    assert!(
        abi.validate(&signature)
            .unwrap_err()
            .contains("complete source storage")
    );
    abi = fixture::descriptor();
    abi.arguments[1].bindings[0].source_offset = u64::MAX;
    assert!(abi.validate(&signature).unwrap_err().contains("overflows"));
    abi = fixture::descriptor();
    abi.arguments[3].align = 3;
    assert!(abi.validate(&signature).unwrap_err().contains("alignment"));
}
#[test]
fn typed_abi_is_part_of_both_module_digests_and_function_pointer_equality() {
    let a = fixture::module().expect("signature_abi::module: test fixture");
    let mut b = a.clone();
    b.func_types[0].abi.as_mut().unwrap().result.size = 32;
    assert_ne!(a.stable_digest(), b.stable_digest());
    assert_ne!(
        a.executable_content_digest_v1(),
        b.executable_content_digest_v1()
    );
    let ty = trust_ir::Ty::Func(trust_ir::FuncTyId::new(0));
    assert!(!trust_ir::ty_structurally_eq_across(&a, &ty, &b, &ty));
    assert_ne!(a.func_types[0], b.func_types[0]);
}
#[test]
fn absence_and_explicit_no_extension_are_distinct() {
    let mut recorded = fixture::signature();
    if let AbiPassMode::Direct(s) = &mut recorded.abi.as_mut().unwrap().arguments[1].mode {
        s.attributes.extension = AbiExtension::None;
    }
    let mut absent = recorded.clone();
    absent.abi = None;
    assert_ne!(recorded, absent);
    let mut legacy = serde_json::to_value(&absent).unwrap();
    legacy.as_object_mut().unwrap().remove("abi");
    assert_eq!(
        serde_json::from_value::<trust_ir::FuncTy>(legacy).unwrap(),
        absent
    );
}

#[test]
fn outer_signature_reader_cannot_drop_unknown_or_misspelled_abi_fields() {
    let signature = fixture::signature();
    let canonical = serde_json::to_value(&signature).unwrap();
    assert_eq!(
        serde_json::from_value::<trust_ir::FuncTy>(canonical.clone()).unwrap(),
        signature
    );
    for field in ["Abi", "signature_abi", "abi_typo"] {
        let mut mutant = canonical.clone();
        let object = mutant.as_object_mut().unwrap();
        let descriptor = object.remove("abi").unwrap();
        object.insert(field.into(), descriptor);
        let text = serde_json::to_string(&mutant).unwrap();
        assert!(
            serde_json::from_str::<trust_ir::FuncTy>(&text).is_err(),
            "unknown field {field} must not become abi=None"
        );
        let encoded = rmp_serde::to_vec_named(&mutant).unwrap();
        assert!(rmp_serde::from_slice::<trust_ir::FuncTy>(&encoded).is_err());
    }
    let mut retained = canonical;
    retained
        .as_object_mut()
        .unwrap()
        .insert("future_abi_contract".into(), serde_json::Value::Bool(true));
    assert!(serde_json::from_value::<trust_ir::FuncTy>(retained.clone()).is_err());
    assert!(
        rmp_serde::from_slice::<trust_ir::FuncTy>(&rmp_serde::to_vec_named(&retained).unwrap())
            .is_err()
    );
    // Legacy absence remains representable; only an actual absent field is
    // defaulted, never an unknown field that could carry transport claims.
    let mut legacy = signature.clone();
    legacy.abi = None;
    let json = serde_json::to_string(&legacy).unwrap();
    assert_eq!(
        serde_json::from_str::<trust_ir::FuncTy>(&json).unwrap(),
        legacy
    );
    let mut missing = serde_json::to_value(&legacy).unwrap();
    missing.as_object_mut().unwrap().remove("abi");
    assert_eq!(
        serde_json::from_value::<trust_ir::FuncTy>(missing.clone()).unwrap(),
        legacy
    );
    assert_eq!(
        rmp_serde::from_slice::<trust_ir::FuncTy>(&rmp_serde::to_vec_named(&missing).unwrap())
            .unwrap(),
        legacy
    );
}
#[test]
fn signature_target_and_recorded_function_facts_must_agree() {
    let m = fixture::module().expect("signature_abi::module: test fixture");
    let abi = m.func_types[0].abi.as_ref().unwrap();
    abi.validate_target(m.target_info.as_ref()).unwrap();
    let mut target = m.target_info.clone().unwrap();
    target.pointer_size = 4;
    assert!(abi.validate_target(Some(&target)).is_err());
    assert!(abi.validate_target(None).is_err());
    let mut f = trust_ir::Function::new(
        trust_ir::FuncId::new(0),
        "callee",
        trust_ir::FuncTyId::new(0),
        trust_ir::BlockId::new(0),
    );
    f.attrs.params = vec![trust_ir::ParamAttrs::default(); 6];
    f.attrs.params[0].sret = true;
    f.attrs.params[1].ext = trust_ir::ArgExt::SignExt;
    abi.reconcile_function(&f).unwrap();
    f.attrs.params[1].ext = trust_ir::ArgExt::ZeroExt;
    assert!(abi.reconcile_function(&f).unwrap_err().contains("disagree"));
    f.attrs.params[1].ext = trust_ir::ArgExt::None;
    f.attrs.params[2].sret = true;
    assert!(abi.reconcile_function(&f).unwrap_err().contains("role"));
}

#[test]
fn serde_refuses_unknown_duplicate_and_missing_descriptor_facts() {
    let text = serde_json::to_string(&fixture::descriptor()).unwrap();
    for mutant in [
        text.replacen("\"fixed_count\":5", "\"fixed_count\":5,\"extra\":0", 1),
        text.replacen(
            "\"fixed_count\":5",
            "\"fixed_count\":5,\"fixed_count\":5",
            1,
        ),
        text.replacen("\"fixed_count\":5,", "", 1),
        text.replacen("\"pointee_align\":null", "", 1)
            .replace(",}", "}"),
        text.replacen("\"rest_offset\":null,", "", 1),
        text.replacen("\"metadata_attributes\":null,", "", 1),
    ] {
        serde_json::from_str::<serde_json::Value>(&mutant).expect("mutation remains valid JSON");
        assert!(serde_json::from_str::<SignatureAbi>(&mutant).is_err());
    }
}

#[test]
fn ignored_nonzero_layout_and_disjoint_tuple_carriers_are_retained() {
    let mut signature = fixture::signature();
    let mut abi = fixture::descriptor();
    abi.arguments[0].size = 32;
    abi.arguments[0].align = 16;
    // Two original arguments share one tuple parameter at disjoint offsets.
    signature.params[2] = trust_ir::Ty::Tuple(vec![trust_ir::Ty::U64, trust_ir::Ty::F64]);
    signature.params.remove(3);
    abi.arguments[2].bindings[1].place = AbiBindingPlace::Parameter(2);
    abi.arguments[2].bindings[1].carrier_offset = 8;
    abi.arguments[3].bindings[0].place = AbiBindingPlace::Parameter(3);
    abi.arguments[4].bindings[0].place = AbiBindingPlace::Parameter(4);
    let mut second = abi.arguments[2].clone();
    second.size = 8;
    second.mode = match &second.mode {
        AbiPassMode::Pair(_, b) => {
            let mut b = b.clone();
            b.source_offset = 0;
            AbiPassMode::Direct(b)
        }
        _ => unreachable!(),
    };
    second.bindings.remove(0);
    second.bindings[0].source_offset = 0;
    abi.arguments[2].size = 8;
    abi.arguments[2].mode = match &abi.arguments[2].mode {
        AbiPassMode::Pair(a, _) => AbiPassMode::Direct(a.clone()),
        _ => unreachable!(),
    };
    abi.arguments[2].bindings.pop();
    abi.arguments.insert(3, second);
    abi.fixed_count += 1;
    abi.validate(&signature).unwrap();
    let mut overlap = abi.clone();
    overlap.arguments[3].bindings[0].carrier_offset = 4;
    assert!(
        overlap
            .validate(&signature)
            .unwrap_err()
            .contains("overlaps")
    );
    let mut overflow = abi.clone();
    overflow.arguments[3].bindings[0].carrier_offset = u64::MAX;
    assert!(
        overflow
            .validate(&signature)
            .unwrap_err()
            .contains("overflows")
    );
    abi.target.features.reverse();
    assert!(abi.validate(&signature).unwrap_err().contains("sorted"));
}

#[test]
fn scalar_defined_bits_distinguish_bool_and_byte_and_reject_invalid_widths() {
    let signature = fixture::signature();
    let base = fixture::descriptor();
    let mut boolean = base.clone();
    let AbiPassMode::Direct(scalar) = &mut boolean.arguments[1].mode else {
        unreachable!()
    };
    scalar.value_bits = 1;
    boolean.validate(&signature).unwrap();
    assert_ne!(boolean.to_canonical_text(), base.to_canonical_text());
    for bits in [0, 9, u16::MAX] {
        let AbiPassMode::Direct(scalar) = &mut boolean.arguments[1].mode else {
            unreachable!()
        };
        scalar.value_bits = bits;
        assert!(
            boolean
                .validate(&signature)
                .unwrap_err()
                .contains("defined-bit")
        );
    }
}

#[test]
fn source_lane_cannot_claim_more_bytes_than_its_actual_carrier() {
    let mut signature = fixture::signature();
    let mut abi = fixture::descriptor();
    signature.params[2] = trust_ir::Ty::U32;
    abi.arguments[2].bindings[0].carrier_bytes = 4;
    assert!(
        abi.validate(&signature)
            .unwrap_err()
            .contains("omits a pair source lane")
    );
}
#[test]
fn oversized_descriptor_refuses_before_fallible_binary_projection() {
    let mut module = fixture::module().expect("signature_abi::module: test fixture");
    assert!(module.first_signature_abi_encoding_error().is_none());
    let unused = module.func_types[0].clone();
    module.func_types.push(unused);
    module.func_types[1].abi.as_mut().unwrap().frontend.revision =
        "x".repeat(MAX_ABI_TEXT_BYTES + 1);
    assert!(matches!(
        module.first_signature_abi_encoding_error(),
        Some((1, _))
    ));
    assert!(
        module.func_types[1]
            .abi
            .as_ref()
            .unwrap()
            .validate(&module.func_types[1])
            .is_err()
    );
    let error = trust_ir::binary::ProjectedModuleBinaryPlan::try_new(
        &module,
        trust_ir::binary::ModuleBinaryOptions::default(),
    )
    .err()
    .expect("fallible preparation refuses oversized descriptor");
    assert!(matches!(
        error,
        trust_ir::binary::BinaryProjectionError::SignatureAbiUnencodable { signature: 1, .. }
    ));
}

#[test]
fn indirect_argument_requires_a_typed_pointer_carrier() {
    let mut signature = fixture::signature();
    signature.params[5] = trust_ir::Ty::U64;
    assert!(
        fixture::descriptor()
            .validate(&signature)
            .unwrap_err()
            .contains("prelowered Ptr")
    );
}

#[test]
fn nonvariadic_fixed_count_preserves_untupled_tail_and_hidden_caller_location() {
    let signature = fixture::signature();
    for (source_abi, fixed_count) in [("RustCall", 1), ("Rust", 4)] {
        let mut abi = fixture::descriptor();
        abi.source_abi = source_abi.into();
        abi.fixed_count = fixed_count;
        assert!(!abi.variadic);
        assert!(abi.fixed_count < abi.arguments.len() as u32);
        abi.validate(&signature).unwrap();
        assert_eq!(
            SignatureAbi::from_canonical_text(&abi.to_canonical_text()).unwrap(),
            abi
        );
    }
    let mut invalid = fixture::descriptor();
    invalid.fixed_count = invalid.arguments.len() as u32 + 1;
    assert!(
        invalid
            .validate(&signature)
            .unwrap_err()
            .contains("fixed argument census")
    );
}

#[test]
fn reference_interpreter_refuses_typed_byval_before_shared_pointer_side_effects() {
    use trust_ir::interpret::{InterpretErrorCode, Interpreter};
    use trust_ir::{
        Block, BlockId, Constant, FuncId, FuncTy, Function, Inst, InstrNode, Ty, ValueId,
    };
    let v = ValueId::new;
    let mut module = fixture::module().expect("signature_abi::module: test fixture");
    module.func_types.clear();
    let mut abi = fixture::descriptor();
    abi.arguments = vec![abi.arguments[4].clone()];
    abi.arguments[0].bindings[0].place = AbiBindingPlace::Parameter(0);
    abi.fixed_count = 1;
    abi.result = AbiArgument {
        size: 0,
        align: 1,
        mode: AbiPassMode::Ignore,
        bindings: vec![],
    };
    let mutator_ty = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            is_vararg: false,
            abi: Some(abi),
        })
        .expect("Module::add_func_type: test fixture");
    module.func_types[mutator_ty.as_usize()]
        .abi
        .as_ref()
        .unwrap()
        .validate(&module.func_types[mutator_ty.as_usize()])
        .unwrap();
    let entry_ty = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::I64],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let mut entry = Function::new(FuncId::new(0), "main", entry_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0));
    b.body = vec![
        InstrNode::new(Inst::Alloca {
            ty: Ty::Tuple(vec![Ty::I64; 3]),
            count: None,
            align: Some(8),
        })
        .with_result(v(0)),
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(8),
        }),
        InstrNode::new(Inst::Call {
            callee: FuncId::new(1),
            args: vec![v(0)],
        }),
        InstrNode::new(Inst::Load {
            ty: Ty::I64,
            ptr: v(0),
            volatile: false,
            align: Some(8),
        })
        .with_result(v(2)),
        InstrNode::new(Inst::Return { values: vec![v(2)] }),
    ];
    entry.blocks.push(b);
    module
        .try_add_function(entry)
        .expect("Module::try_add_function: test fixture");
    let mut mutator = Function::new(FuncId::new(1), "mutate_copy", mutator_ty, BlockId::new(0));
    let mut b = Block::new(BlockId::new(0)).with_param(v(0), Ty::Ptr);
    b.body = vec![
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(99),
        })
        .with_result(v(1)),
        InstrNode::new(Inst::Store {
            ty: Ty::I64,
            ptr: v(0),
            value: v(1),
            volatile: false,
            align: Some(8),
        }),
        InstrNode::new(Inst::Return { values: vec![] }),
    ];
    mutator.blocks.push(b);
    module
        .try_add_function(mutator)
        .expect("Module::try_add_function: test fixture");
    let interpreter = Interpreter::with_module(&module);
    for result in [
        interpreter.execute_func(FuncId::new(0), []),
        interpreter.execute_function(&module.functions[0], []),
    ] {
        let error = result.unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UnsupportedCall);
        assert!(error.message.contains("typed signature ABI transport"));
    }
    // Mutation control: deleting the record executes ordinary pointer semantics,
    // changing the caller's storage to99. A proper by-value call would leave7.
    let mut erased = module.clone();
    erased.func_types[mutator_ty.as_usize()].abi = None;
    let outcome = Interpreter::with_module(&erased)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(outcome.returns[0].as_int().unwrap().as_signed(), 99);
    // An unused or function-pointer-only signature must not escape the module
    // census merely because the selected entry has a legacy signature.
    module.functions.truncate(1);
    module.functions[0].blocks[0]
        .body
        .retain(|n| !matches!(n.inst, Inst::Call { .. }));
    assert!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap_err()
            .message
            .contains("typed signature ABI transport")
    );
}

/// D1a: a typed signature ABI past its encoding limits is refused by the
/// writer's own `func_types` arm (`docs/SPEC_RATIFICATIONS.md`, "A construct
/// or count with no wire image is refused by the writer's own arm, at every
/// trust-ir entry point"), by the reader's own predicate
/// (`SignatureAbi::validate_encoding_limits`), so the one pre-check
/// (`Module::wire_image_refusal`) names it and no writer emits a blob its
/// reader refuses.
///
/// Kind (i) for the node budget: before D1a the writer's arm asserted only
/// the byte limit, so `serialize_module` returned a blob for a descriptor
/// within the byte limit and past the node budget, and `deserialize_module`
/// refused that blob; the hand-written pre-checks (`try_new`,
/// `wire_identity_blocker`) refused the module while the writer wrote it.
/// Mutation check: an arm that writes the text without the predicate (or
/// checks only the byte limit) turns the `serialize_module` assertion red.
#[test]
fn a_descriptor_past_its_limits_is_the_writers_own_refusal() {
    use std::panic::{AssertUnwindSafe, catch_unwind};
    use trust_ir::BinaryProjectionError;

    let control = fixture::module().expect("signature_abi::module: test fixture");
    assert_eq!(control.wire_image_refusal(), None);
    let bytes = serialize_module(&control).expect("serialize_module: test fixture");
    assert_eq!(deserialize_module(&bytes).unwrap(), control);

    let mut nodes = fixture::module().expect("signature_abi::module: test fixture");
    nodes.func_types[0].abi.as_mut().unwrap().target.features = vec!["n".to_owned(); 70_000];
    let abi = nodes.func_types[0].abi.as_ref().unwrap();
    assert!(
        abi.to_canonical_text().len() <= MAX_ABI_TEXT_BYTES,
        "within the byte limit: only the node budget refuses it"
    );
    let (signature, detail) = nodes
        .first_signature_abi_encoding_error()
        .expect("past the node budget");
    assert_eq!(
        nodes.wire_image_refusal(),
        Some(BinaryProjectionError::SignatureAbiUnencodable {
            signature,
            detail: detail.clone(),
        })
    );
    assert_eq!(
        catch_unwind(AssertUnwindSafe(|| serialize_module(&nodes)))
            .expect("serialize_module never panics")
            .err(),
        Some(BinaryProjectionError::SignatureAbiUnencodable {
            signature,
            detail: detail.clone(),
        }),
        "no blob a reader would refuse is emitted: the blob entry refuses by name"
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| nodes.stable_digest())).is_err(),
        "a module with no wire image has no identity"
    );

    // Precedence: a carrier a pre-check already reported before v60 keeps
    // its place ahead of the descriptor, and `Ty::Error` (first reported by
    // D1a) ranks after it.
    let mut all = nodes.clone();
    all.completeness = Some(trust_ir::ModuleCompleteness::Complete);
    all.types.push(trust_ir::Ty::Error);
    assert_eq!(
        all.wire_image_refusals(),
        vec![
            BinaryProjectionError::CompletenessClaimUnencodable,
            BinaryProjectionError::SignatureAbiUnencodable { signature, detail },
            BinaryProjectionError::ProducerInternalType,
        ]
    );
}
