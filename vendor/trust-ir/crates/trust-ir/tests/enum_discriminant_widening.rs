//! Existing logical enum/tag/widen/Switch path; no Rust/physical ABI theorem.
use trust_ir::interpret::{
    InterpretOptions, InterpretOutcome, InterpretValue, InterpretValueKind, Interpreter,
};
use trust_ir::ty::{EnumDef, EnumTagRepr, EnumVariant, FuncTy, Ty};
use trust_ir::value::{BlockId, EnumId, FuncId, FuncTyId, ValueId};
use trust_ir::{Block, CastOp, Constant, Function, Inst, InstrNode, Module, SwitchCase};
fn value(n: u32) -> ValueId {
    ValueId::new(n)
}
fn block(n: u32) -> BlockId {
    BlockId::new(n)
}
fn fixture(pointer_bytes: u32, signed: bool, cast: CastOp) -> Module {
    let mut module = Module::new("declared-discriminant-widening");
    module.target_info = Some(trust_ir::TargetInfo {
        triple: if pointer_bytes == 4 {
            "wasm32-unknown-unknown"
        } else {
            "aarch64-apple-darwin"
        }
        .into(),
        pointer_size: pointer_bytes,
        endianness: trust_ir::Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    });
    let discs = if signed { [-7, 42] } else { [250, 42] };
    module.add_enum(
        EnumDef::new(
            EnumId::new(7),
            "Declared",
            vec![
                EnumVariant {
                    name: "First".into(),
                    fields: vec![Ty::U64],
                    field_names: vec![],
                },
                EnumVariant {
                    name: "Second".into(),
                    fields: vec![Ty::U64],
                    field_names: vec![],
                },
            ],
        )
        .with_discriminants(discs.into_iter().map(Some).collect())
        .with_repr(if signed {
            EnumTagRepr::I8
        } else {
            EnumTagRepr::U8
        }),
    );
    module
        .add_func_type(FuncTy::unrecorded(
            vec![Ty::Enum(EnumId::new(7))],
            vec![Ty::Isize, Ty::U64, Ty::U64],
            false,
        ))
        .unwrap();
    let tag = if signed { Ty::I8 } else { Ty::U8 };
    let mut function = Function::new(
        FuncId::new(0),
        "read_and_switch",
        FuncTyId::new(0),
        block(0),
    );
    let mut entry = Block::new(block(0)).with_param(value(0), Ty::Enum(EnumId::new(7)));
    entry.body = vec![
        InstrNode::new(Inst::ExtractField {
            ty: tag.clone(),
            aggregate: value(0),
            field: 0,
        })
        .with_result(value(1)),
        // A real active-field read supplies declaration/variant membership.
        InstrNode::new(Inst::ExtractField {
            ty: Ty::U64,
            aggregate: value(0),
            field: 1,
        })
        .with_result(value(2)),
        InstrNode::new(Inst::Cast {
            op: cast,
            src_ty: tag,
            dst_ty: Ty::Isize,
            operand: value(1),
        })
        .with_result(value(3)),
        InstrNode::new(Inst::Switch {
            value: value(3),
            default: block(3),
            default_args: vec![value(3), value(2)],
            cases: discs
                .into_iter()
                .enumerate()
                .map(|(i, disc)| SwitchCase {
                    value: Constant::Int(disc),
                    target: block(i as u32 + 1),
                    args: vec![value(3), value(2)],
                })
                .collect(),
            exhaustive_enum_unreachable: false,
        }),
    ];
    function.blocks.push(entry);
    for id in 1..=3 {
        let start = id * 10;
        let mut b = Block::new(block(id))
            .with_param(value(start), Ty::Isize)
            .with_param(value(start + 1), Ty::U64);
        b.body = vec![
            InstrNode::new(Inst::Const {
                ty: Ty::U64,
                value: Constant::Int(i128::from(id)),
            })
            .with_result(value(start + 2)),
            InstrNode::new(Inst::Return {
                values: vec![value(start), value(start + 1), value(start + 2)],
            }),
        ];
        function.blocks.push(b);
    }
    module.try_add_function(function).unwrap();
    module
}
fn argument(signed: bool, disc: i128) -> InterpretValue {
    InterpretValue {
        ty: Ty::Enum(EnumId::new(7)),
        kind: InterpretValueKind::Aggregate(vec![
            InterpretValue::int(if signed { Ty::I8 } else { Ty::U8 }, disc).unwrap(),
            InterpretValue::int(Ty::U64, 91).unwrap(),
        ]),
    }
}
fn run(
    module: &Module,
    arg: InterpretValue,
) -> Result<InterpretOutcome, trust_ir::interpret::InterpretError> {
    Interpreter::with_module(module)
        .with_options(InterpretOptions {
            fuel: 32,
            max_call_depth: 4,
            ..Default::default()
        })
        .execute_func(FuncId::new(0), [arg])
}
#[test]
fn declaration_signedness_controls_negative_and_unsigned_high_bit_at_both_target_widths() {
    for bytes in [4, 8] {
        for signed in [false, true] {
            let module = fixture(
                bytes,
                signed,
                if signed { CastOp::SExt } else { CastOp::ZExt },
            );
            for (disc, branch) in [(if signed { -7 } else { 250 }, 1), (42, 2)] {
                let result = run(&module, argument(signed, disc)).unwrap();
                assert_eq!(result.host_calls, 0);
                assert_eq!(result.returns[0].as_int().unwrap().bits, bytes * 8);
                assert_eq!(result.returns[0].as_int().unwrap().as_signed(), disc);
                assert_eq!(result.returns[1].as_int().unwrap().as_unsigned(), 91);
                assert_eq!(result.returns[2].as_int().unwrap().as_unsigned(), branch);
            }
        }
    }
}
#[test]
fn wrong_extension_selects_the_default_instead_of_the_declared_noncontiguous_arm() {
    for bytes in [4, 8] {
        for signed in [false, true] {
            let module = fixture(
                bytes,
                signed,
                if signed { CastOp::ZExt } else { CastOp::SExt },
            );
            let result = run(&module, argument(signed, if signed { -7 } else { 250 })).unwrap();
            assert_eq!(result.returns[2].as_int().unwrap().as_unsigned(), 3);
        }
    }
}
#[test]
fn unknown_tag_nominal_and_wrong_payload_type_refuse_before_cast_and_switch() {
    let module = fixture(8, true, CastOp::SExt);
    for mutation in 0..3 {
        let mut arg = argument(true, -7);
        match mutation {
            0 => {
                if let InterpretValueKind::Aggregate(lanes) = &mut arg.kind {
                    lanes[0] = InterpretValue::int(Ty::I8, 12).unwrap();
                }
            }
            1 => arg.ty = Ty::Enum(EnumId::new(8)),
            2 => {
                if let InterpretValueKind::Aggregate(lanes) = &mut arg.kind {
                    lanes[1] = InterpretValue::bool(true);
                }
            }
            _ => unreachable!(),
        }
        assert!(run(&module, arg).is_err(), "mutation {mutation}");
    }
}

#[test]
fn malformed_raw_integer_tag_is_refused_instead_of_aliasing_a_declared_negative_tag() {
    let module = fixture(8, true, CastOp::SExt);
    let mut arg = argument(true, -7);
    let InterpretValueKind::Aggregate(lanes) = &mut arg.kind else {
        unreachable!()
    };
    lanes[0].kind = InterpretValueKind::Int(trust_ir::interpret::InterpretInt {
        bits: 8,
        signed: true,
        raw: 505,
    });
    let result = run(&module, arg);
    assert!(
        result.is_err(),
        "out-of-range i8 raw505 must not alias canonical -7: {result:?}"
    );
}

#[test]
fn unsigned_pointer_source_width_preserves_its_value_when_entering_a_wider_target() {
    let mut module = Module::new("unsigned-entry-width");
    module
        .add_func_type(FuncTy::unrecorded(vec![Ty::Usize], vec![Ty::Usize], false))
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "identity", FuncTyId::new(0), block(0));
    let mut entry = Block::new(block(0)).with_param(value(0), Ty::Usize);
    entry.body.push(InstrNode::new(Inst::Return {
        values: vec![value(0)],
    }));
    function.blocks.push(entry);
    module.try_add_function(function).unwrap();
    let input = InterpretValue::int_at(Ty::Usize, i128::from(u32::MAX), 32).unwrap();
    let out = run(&module, input).unwrap();
    assert_eq!(out.returns[0].as_int().unwrap().bits, 64);
    assert_eq!(
        out.returns[0].as_int().unwrap().as_unsigned(),
        u128::from(u32::MAX)
    );
}

fn identity(ty: Ty, pointer_bytes: u32, declaration: bool) -> Module {
    let mut module = Module::new("entry-integer-carrier");
    module.target_info = fixture(pointer_bytes, true, CastOp::SExt).target_info;
    module
        .add_func_type(FuncTy::unrecorded(
            vec![ty.clone()],
            vec![ty.clone()],
            false,
        ))
        .unwrap();
    let mut function = Function::new(FuncId::new(0), "entry", FuncTyId::new(0), block(0));
    if !declaration {
        let mut entry = Block::new(block(0)).with_param(value(0), ty);
        entry.body.push(InstrNode::new(Inst::Return {
            values: vec![value(0)],
        }));
        function.blocks.push(entry);
    }
    module.try_add_function(function).unwrap();
    module
}
struct CountingHost(std::sync::atomic::AtomicUsize);
impl trust_ir::interpret::HostCalls for CountingHost {
    fn call(
        &self,
        _callee: &Function,
        _sig: &FuncTy,
        args: &[InterpretValue],
        _host: &mut trust_ir::interpret::HostState,
    ) -> Option<trust_ir::interpret::InterpretResult<Vec<InterpretValue>>> {
        self.0.fetch_add(1, std::sync::atomic::Ordering::SeqCst);
        Some(Ok(args.to_vec()))
    }
}
#[test]
fn malformed_width_sign_kind_and_raw_fail_before_a_host_callback() {
    use trust_ir::interpret::{InterpretErrorCode, InterpretInt};
    for (ty, bits, signed, raw) in [
        (Ty::I8, 0, true, 0),
        (Ty::I8, 129, true, 0),
        (Ty::I8, 64, true, 42),
        (Ty::I8, 8, false, 42),
        (Ty::I8, 8, true, 505),
        (Ty::Usize, 0, false, 0),
        (Ty::Usize, 32, true, 42),
        (Ty::Usize, 64, false, 1u128 << 65),
        (Ty::Char, 64, false, 0xd800),
        (Ty::Char, 32, true, 65),
        (Ty::Char, 32, false, 1u128 << 32),
    ] {
        let module = identity(ty.clone(), 8, true);
        let host = CountingHost(Default::default());
        let arg = InterpretValue {
            ty,
            kind: InterpretValueKind::Int(InterpretInt { bits, signed, raw }),
        };
        let error = Interpreter::with_module(&module)
            .with_host(&host)
            .execute_func(FuncId::new(0), [arg])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::TypeError);
        assert_eq!(host.0.load(std::sync::atomic::Ordering::SeqCst), 0);
    }
    let module = identity(Ty::I8, 8, true);
    let host = CountingHost(Default::default());
    let error = Interpreter::with_module(&module)
        .with_host(&host)
        .execute_func(
            FuncId::new(0),
            [InterpretValue {
                ty: Ty::I8,
                kind: InterpretValueKind::Bool(true),
            }],
        )
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::TypeError);
    assert_eq!(host.0.load(std::sync::atomic::Ordering::SeqCst), 0);
}
#[test]
fn signed_and_unsigned_source_widths_keep_math_and_refuse_target_overflow() {
    for (signed, source_bits, bytes, input, fits) in [
        (false, 8, 4, 250, true),
        (false, 8, 8, 250, true),
        (false, 32, 8, i128::from(u32::MAX), true),
        (false, 64, 4, i128::from(u32::MAX), true),
        (false, 64, 4, i128::from(u32::MAX) + 1, false),
        (true, 32, 8, -7, true),
        (true, 64, 4, -7, true),
        (true, 64, 4, i128::from(i32::MAX) + 1, false),
        (false, 128, 8, i128::from(u64::MAX), true),
        (true, 128, 8, i128::from(i64::MIN), true),
        (true, 128, 8, i128::from(i64::MAX) + 1, false),
    ] {
        let ty = if signed { Ty::Isize } else { Ty::Usize };
        let module = identity(ty.clone(), bytes, false);
        let result = run(
            &module,
            InterpretValue::int_at(ty, input, source_bits).unwrap(),
        );
        if !fits {
            assert!(result.is_err());
            continue;
        }
        let int = result.unwrap().returns[0].as_int().unwrap();
        assert_eq!(int.bits, bytes * 8);
        assert_eq!(int.signed, signed);
        if signed {
            assert_eq!(int.as_signed(), input);
        } else {
            assert_eq!(int.as_unsigned(), input as u128);
        }
    }
}
#[test]
fn poison_and_unminted_handles_keep_their_existing_ownership_error() {
    use trust_ir::interpret::InterpretErrorCode;
    for kind in [
        InterpretValueKind::PartialBytes(vec![None]),
        InterpretValueKind::Uninit,
        InterpretValueKind::Handle { id: 0 },
    ] {
        let module = identity(Ty::I8, 8, true);
        let host = CountingHost(Default::default());
        let error = Interpreter::with_module(&module)
            .with_host(&host)
            .execute_func(FuncId::new(0), [InterpretValue { ty: Ty::I8, kind }])
            .unwrap_err();
        assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
        assert_eq!(host.0.load(std::sync::atomic::Ordering::SeqCst), 0);
    }
}
#[test]
fn source_width_conversion_visits_sparse_stored_values_not_the_logical_length() {
    use trust_ir::interpret::ArrayValue;
    let len = 1u64 << 40;
    let mut module = identity(Ty::Unit, 8, false);
    let element = module.add_type(Ty::Usize).unwrap();
    let ty = Ty::Array(element, len);
    module.func_types[0].params[0] = ty.clone();
    module.func_types[0].returns[0] = ty.clone();
    module.functions[0].blocks[0].params[0].1 = ty.clone();
    let arg = InterpretValue {
        ty,
        kind: InterpretValueKind::Array(ArrayValue::splat(
            InterpretValue::int_at(Ty::Usize, i128::from(u32::MAX), 32).unwrap(),
            len,
        )),
    };
    let result = run(&module, arg).unwrap();
    let InterpretValueKind::Array(values) = &result.returns[0].kind else {
        panic!("array result")
    };
    assert_eq!(values.len(), len);
    assert_eq!(
        values.get(len - 1).unwrap().as_int().unwrap().as_unsigned(),
        u128::from(u32::MAX)
    );
    let mut stored = 0;
    let _ = values.try_for_each_stored(|_| {
        stored += 1;
        std::ops::ControlFlow::<()>::Continue(())
    });
    assert_eq!(stored, 1);
}

#[test]
fn canonical_wire_keeps_the_declaration_tag_extension_and_target_width() {
    for bytes in [4, 8] {
        for signed in [false, true] {
            let module = fixture(
                bytes,
                signed,
                if signed { CastOp::SExt } else { CastOp::ZExt },
            );
            let encoded = trust_ir::binary::serialize_module(&module).unwrap();
            let decoded = trust_ir::binary::deserialize_module(&encoded).unwrap();
            for disc in [if signed { -7 } else { 250 }, 42] {
                assert_eq!(
                    run(&module, argument(signed, disc)).unwrap().returns,
                    run(&decoded, argument(signed, disc)).unwrap().returns
                );
            }
        }
    }
}

#[test]
fn unicode_entry_domain_keeps_ub_and_prevents_host_callbacks() {
    use trust_ir::interpret::{InterpretErrorCode, InterpretInt};
    for declaration in [false, true] {
        for raw in [0xd800, 0xdfff, 0x110000] {
            let module = identity(Ty::Char, 8, declaration);
            let host = CountingHost(Default::default());
            let arg = InterpretValue {
                ty: Ty::Char,
                kind: InterpretValueKind::Int(InterpretInt {
                    bits: 32,
                    signed: false,
                    raw,
                }),
            };
            let error = Interpreter::with_module(&module)
                .with_host(&host)
                .execute_func(FuncId::new(0), [arg])
                .unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::UndefinedBehavior);
            assert_eq!(host.0.load(std::sync::atomic::Ordering::SeqCst), 0);
        }
        for raw in [0xd7ff, 0xe000, 0x10ffff] {
            let module = identity(Ty::Char, 8, declaration);
            let host = CountingHost(Default::default());
            let arg = InterpretValue::int(Ty::Char, raw).unwrap();
            let outcome = Interpreter::with_module(&module)
                .with_host(&host)
                .execute_func(FuncId::new(0), [arg])
                .unwrap();
            assert_eq!(outcome.returns[0].as_int().unwrap().raw, raw as u128);
            assert_eq!(
                host.0.load(std::sync::atomic::Ordering::SeqCst),
                usize::from(declaration)
            );
        }
    }
}
