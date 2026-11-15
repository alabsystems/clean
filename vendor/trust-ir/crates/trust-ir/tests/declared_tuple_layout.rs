use trust_ir::interpret::{InterpretErrorCode, Interpreter};
use trust_ir::{
    Block, BlockId, Constant, Endianness, FuncId, FuncTy, Function, Inst, InstrNode, Module,
    TargetInfo, TupleLayoutDescriptor, Ty, TyId, TyLayoutKind, ValueId,
};

type RustTuple = (u8, u64, u8);

fn target() -> TargetInfo {
    TargetInfo {
        triple: if cfg!(all(target_arch = "aarch64", target_os = "macos")) {
            "aarch64-apple-darwin"
        } else {
            "x86_64-unknown-linux-gnu"
        }
        .into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}

fn observed() -> (Module, Ty) {
    let mut module = Module::new("declared_tuple");
    module.target_info = Some(target());
    let ty = Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::U8]);
    let tuple_type = module
        .add_type(ty.clone())
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type,
        size: std::mem::size_of::<RustTuple>() as u64,
        align: std::mem::align_of::<RustTuple>() as u64,
        field_offsets: vec![
            std::mem::offset_of!(RustTuple, 0) as u64,
            std::mem::offset_of!(RustTuple, 1) as u64,
            std::mem::offset_of!(RustTuple, 2) as u64,
        ],
    });
    (module, ty)
}

#[test]
fn declared_tuple_uses_compiler_observed_offsets() {
    let (module, ty) = observed();
    module.validate_tuple_layouts().unwrap();
    let shape = module.ty_layout_shape(&ty).unwrap();
    assert_eq!(
        shape.size_bytes(),
        Some(std::mem::size_of::<RustTuple>() as u64)
    );
    let TyLayoutKind::Tuple { fields } = shape.kind else {
        panic!("tuple kind lost")
    };
    assert_eq!(
        fields
            .iter()
            .map(|f| f.offset_bits.unwrap() / 8)
            .collect::<Vec<_>>(),
        module.tuple_layouts[0].field_offsets
    );
    // This observed Rust layout is the counterexample to declaration-order C.
    assert_ne!(module.tuple_layouts[0].field_offsets, vec![0, 8, 16]);
}

#[test]
fn declared_tuple_array_layout_keeps_independent_cycle_guards() {
    let (mut module, _) = observed();
    let tuple = module.tuple_layouts[0].tuple_type;
    let array = Ty::Array(tuple, 3);
    assert_eq!(
        module.ty_layout_shape(&array).unwrap().size_bytes(),
        Some(3 * std::mem::size_of::<RustTuple>() as u64)
    );
    // The same array becomes inline-recursive when it is a tuple field.
    module.types[tuple.as_usize()] = Ty::Tuple(vec![array]);
    module.tuple_layouts[0].field_offsets = vec![0];
    assert!(module.validate_tuple_layouts().is_err());
}

#[cfg(all(feature = "binary", feature = "serde"))]
#[test]
fn declared_tuple_v42_preserves_the_published_v41_payload() {
    use trust_ir::binary::{
        BinaryProjectionError, ModuleBinaryBody, ModuleBinaryOptions, ProjectedModuleBinaryPlan,
        deserialize_module, serialize_module,
    };
    use trust_ir::{ModuleImport, ProofDigest};

    let published = include_bytes!("../../trust-ir-conformance/tests/fixtures/body_gate.tmbc");
    let mut module = deserialize_module(published).unwrap();
    assert!(module.tuple_layouts.is_empty());
    assert_eq!(
        serialize_module(&module).expect("serialize_module: test fixture"),
        published
    );
    let old_msgpack = include_bytes!(
        "../../trust-ir-conformance/tests/fixtures/v41-reader-compat/body_gate_v41.msgpack"
    );
    assert_eq!(
        rmp_serde::from_slice::<Module>(old_msgpack).unwrap(),
        module
    );
    let gates: Vec<_> = module
        .functions
        .iter()
        .map(|f| f.body_gate.clone())
        .collect();
    let (source, ty) = observed();
    let mut descriptor = source.tuple_layouts[0].clone();
    descriptor.tuple_type = module.add_type(ty).expect("Module::add_type: test fixture");
    module.target_info = source.target_info;
    module.tuple_layouts.push(descriptor);
    module.global_asm.push(".globl tuple_layout_control".into());
    // A legacy (V2) row: a V3 row would raise the header to v44.
    module
        .intern_import(
            ModuleImport::new("tuple_dependency", ProofDigest::sha256([7; 32]))
                .with_scheme(trust_ir::IdentityScheme::V2),
        )
        .expect("Module::intern_import: test fixture");
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 42);
    let decoded = deserialize_module(&bytes).unwrap();
    assert_eq!(decoded, module);
    assert_eq!(
        decoded
            .functions
            .iter()
            .map(|f| f.body_gate.clone())
            .collect::<Vec<_>>(),
        gates
    );
    assert_eq!(
        serde_json::from_slice::<Module>(&serde_json::to_vec(&module).unwrap()).unwrap(),
        module
    );
    assert_eq!(
        rmp_serde::from_slice::<Module>(&rmp_serde::to_vec(&module).unwrap()).unwrap(),
        module
    );
    for body in [ModuleBinaryBody::RawV38, ModuleBinaryBody::CanonicalV38] {
        assert!(matches!(
            ProjectedModuleBinaryPlan::try_new(
                &module,
                ModuleBinaryOptions {
                    body,
                    ..Default::default()
                }
            ),
            Err(BinaryProjectionError::TupleLayoutRequiresV42)
        ));
    }
    // Reinterpreting a v42 tuple payload as v41 must not silently drop it.
    let mut wrong_version = bytes;
    wrong_version[8..12].copy_from_slice(&41u32.to_le_bytes());
    assert!(deserialize_module(&wrong_version).is_err());
}

#[test]
fn declared_tuple_requires_unique_complete_target_bound_evidence() {
    let (module, ty) = observed();
    let mut absent = module.clone();
    absent.tuple_layouts.clear();
    assert!(absent.ty_layout_shape(&ty).is_err());
    let mut cases = Vec::new();
    let mut x = module.clone();
    x.target_info = None;
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].align = 0;
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].align = 3;
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].size = 15;
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].field_offsets.pop();
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].field_offsets[0] = x.tuple_layouts[0].field_offsets[1];
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].field_offsets[1] = 1;
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].field_offsets[0] = u64::MAX;
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts[0].tuple_type = TyId::new(999);
    cases.push(x);
    let mut x = module.clone();
    x.types[0] = Ty::U64;
    cases.push(x);
    let mut x = module.clone();
    x.tuple_layouts.push(x.tuple_layouts[0].clone());
    cases.push(x);
    let mut x = module.clone();
    let alias = x
        .add_type(ty.clone())
        .expect("Module::add_type: test fixture");
    let mut desc = x.tuple_layouts[0].clone();
    desc.tuple_type = alias;
    x.tuple_layouts.push(desc);
    cases.push(x);
    for (index, invalid) in cases.iter().enumerate() {
        assert!(
            invalid.validate_tuple_layouts().is_err(),
            "accepted malformed case {index}"
        );
    }
}

#[test]
fn declared_tuple_nested_layouts_and_cycles_are_checked() {
    type Outer = (RustTuple, u16);
    let (mut module, inner) = observed();
    let outer = Ty::Tuple(vec![inner, Ty::U16]);
    let tuple_type = module
        .add_type(outer.clone())
        .expect("Module::add_type: test fixture");
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type,
        size: std::mem::size_of::<Outer>() as u64,
        align: std::mem::align_of::<Outer>() as u64,
        field_offsets: vec![
            std::mem::offset_of!(Outer, 0) as u64,
            std::mem::offset_of!(Outer, 1) as u64,
        ],
    });
    module.validate_tuple_layouts().unwrap();
    assert_eq!(
        module.ty_layout_shape(&outer).unwrap().size_bytes(),
        Some(std::mem::size_of::<Outer>() as u64)
    );
    module.tuple_layouts.remove(0);
    assert!(
        module.validate_tuple_layouts().is_err(),
        "missing nested evidence accepted"
    );

    let mut cycle = Module::new("cycle");
    cycle.target_info = Some(target());
    cycle
        .add_type(Ty::Tuple(vec![Ty::Array(TyId::new(0), 1)]))
        .expect("Module::add_type: test fixture");
    cycle.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(0),
        size: 8,
        align: 8,
        field_offsets: vec![0],
    });
    assert!(
        cycle.validate_tuple_layouts().is_err(),
        "inline tuple/array cycle accepted"
    );
}

fn memory_reader() -> Module {
    let (mut module, tuple) = observed();
    let signature = module
        .add_func_type(FuncTy {
            params: vec![],
            returns: vec![Ty::U64],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut function = Function::new(
        FuncId::new(0),
        "read_real_offset",
        signature,
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    let v = ValueId::new;
    let ops = [
        (
            Some(v(0)),
            Inst::Alloca {
                ty: tuple.clone(),
                count: None,
                align: None,
            },
        ),
        (
            Some(v(1)),
            Inst::Const {
                ty: tuple.clone(),
                value: Constant::Aggregate(vec![
                    Constant::Int(17),
                    Constant::Int(0x1122334455667788),
                    Constant::Int(34),
                ]),
            },
        ),
        (
            None,
            Inst::Store {
                ty: tuple,
                ptr: v(0),
                value: v(1),
                volatile: false,
                align: None,
            },
        ),
        (
            Some(v(2)),
            Inst::Const {
                ty: Ty::I64,
                value: Constant::Int(std::mem::offset_of!(RustTuple, 1) as i128),
            },
        ),
        (
            Some(v(3)),
            Inst::GEP {
                pointee_ty: Ty::U8,
                base: v(0),
                indices: vec![v(2)],
                inbounds: true,
            },
        ),
        (
            Some(v(4)),
            Inst::Load {
                ty: Ty::U64,
                ptr: v(3),
                volatile: false,
                align: None,
            },
        ),
        (None, Inst::Return { values: vec![v(4)] }),
    ];
    for (result, inst) in ops {
        let node = InstrNode::new(inst);
        block.body.push(if let Some(value) = result {
            node.with_result(value)
        } else {
            node
        });
    }
    function.blocks.push(block);
    module
        .try_add_function(function)
        .expect("Module::try_add_function: test fixture");
    module
}

#[test]
fn declared_tuple_store_matches_an_independent_rust_field_address() {
    let module = memory_reader();
    let result = Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(
        result.returns[0].as_int().unwrap().as_unsigned(),
        0x1122334455667788
    );
    let mut old = module.clone();
    old.tuple_layouts.clear();
    // Control: under the canonical C-style image the Rust field-1 address
    // does not hold field 1. Where it overlaps C-layout padding (rustc puts
    // the `u64` at 0; C puts `u8` @0 and padding 1..8) the typed tuple
    // `Store` left those bytes UNINITIALIZED (WS2.14 — a typed aggregate
    // store never fabricates padding), so the load is poison and returning
    // it is undefined behaviour; otherwise it reads a different value.
    match Interpreter::with_module(&old).execute_func(FuncId::new(0), []) {
        Ok(result) => assert_ne!(
            result.returns[0].as_int().unwrap().as_unsigned(),
            0x1122334455667788,
            "control must distinguish the old C-style byte image"
        ),
        Err(error) => assert!(
            error.code == InterpretErrorCode::UndefinedBehavior
                && error.message.contains("use of an uninitialized value"),
            "the control may only fail as a poison read of C-layout padding: {error:?}"
        ),
    }
}

#[test]
fn declared_tuple_interpreter_rechecks_unvalidated_metadata() {
    let mut module = memory_reader();
    module.tuple_layouts[0].field_offsets[0] = module.tuple_layouts[0].field_offsets[1];
    assert!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .is_err()
    );
}

#[cfg(all(feature = "binary", feature = "parser"))]
#[test]
fn declared_tuple_round_trips_and_changes_module_identity() {
    use trust_ir::binary::{
        ModuleBinaryBody, ModuleBinaryOptions, ProjectedModuleBinaryPlan, deserialize_module,
        serialize_module,
    };
    let (module, _) = observed();
    let bytes = serialize_module(&module).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(bytes[8..12].try_into().unwrap()), 42);
    assert_eq!(deserialize_module(&bytes).unwrap(), module);
    assert_eq!(
        trust_ir::parser::parse_module(&module.to_string()).unwrap(),
        module
    );
    let options = ModuleBinaryOptions {
        body: ModuleBinaryBody::RawV38,
        ..Default::default()
    };
    assert!(ProjectedModuleBinaryPlan::try_new(&module, options).is_err());
    let mut absent = module.clone();
    absent.tuple_layouts.clear();
    let old = serialize_module(&absent).expect("serialize_module: test fixture");
    assert_eq!(u32::from_le_bytes(old[8..12].try_into().unwrap()), 38);
    assert_ne!(module.stable_digest(), absent.stable_digest());
    let mut invalid = module.clone();
    invalid.tuple_layouts[0].align = 0;
    assert!(
        deserialize_module(&serialize_module(&invalid).expect("serialize_module: test fixture"))
            .is_err()
    );
    let mut changed = module.clone();
    changed.tuple_layouts[0].field_offsets.swap(0, 2);
    changed.validate_tuple_layouts().unwrap();
    assert_ne!(module.stable_digest(), changed.stable_digest());
}

#[cfg(feature = "serde")]
#[test]
fn declared_tuple_serde_preserves_positional_fields() {
    let (module, _) = observed();
    assert_eq!(
        rmp_serde::from_slice::<Module>(&rmp_serde::to_vec(&module).unwrap()).unwrap(),
        module
    );
    let mut empty = module;
    empty.tuple_layouts.clear();
    assert_eq!(
        rmp_serde::from_slice::<Module>(&rmp_serde::to_vec(&empty).unwrap()).unwrap(),
        empty
    );
}

#[cfg(feature = "diff")]
#[test]
fn declared_tuple_diff_reports_unused_layout_semantics_with_proofs_ignored() {
    use trust_ir::diff::{DiffOptions, diff_with};
    let (a, _) = observed();
    assert!(a.functions.is_empty());
    let opts = DiffOptions {
        ignore_proofs: true,
        ..DiffOptions::default()
    };
    // Each variant names the ONE `module_meta` row it must produce. The
    // endianness flip used to surface as a `tuple_layout_target` row that
    // fired only when a tuple table was present; target information is now
    // compared for every module under the `target_info` row (audit row
    // b1.gap.diff_blind_to_spec_modules_and_target).
    let mut variants = Vec::new();
    let mut b = a.clone();
    b.tuple_layouts[0].field_offsets.swap(0, 2);
    variants.push((b, "tuple_layouts"));
    let mut b = a.clone();
    b.tuple_layouts[0].size += 8;
    variants.push((b, "tuple_layouts"));
    let mut b = a.clone();
    b.tuple_layouts[0].align = 16;
    variants.push((b, "tuple_layouts"));
    let mut b = a.clone();
    b.types[0] = Ty::Tuple(vec![Ty::I8, Ty::U64, Ty::U8]);
    variants.push((b, "tuple_layouts"));
    let mut b = a.clone();
    b.tuple_layouts.clear();
    variants.push((b, "tuple_layouts"));
    let mut b = a.clone();
    b.target_info.as_mut().unwrap().endianness = Endianness::Big;
    variants.push((b, "target_info"));
    for (b, field) in variants {
        b.validate_tuple_layouts().unwrap();
        let d = diff_with(&a, &b, opts);
        assert_eq!(d.exit_code(), 1, "{field}");
        assert!(d.changes.is_empty(), "{field}");
        assert!(d.proof_state_changes.is_empty(), "{field}");
        let fields: Vec<&str> = d
            .module_meta_changes
            .iter()
            .map(|m| m.field.as_str())
            .collect();
        assert_eq!(fields, vec![field], "{d:?}");
        assert!(
            d.to_text().contains(&format!("~ module {field}: ")),
            "{field}: {}",
            d.to_text()
        );
        let json: serde_json::Value = serde_json::from_str(&d.to_json()).unwrap();
        assert_eq!(json["module_meta"][0]["field"], field, "{json}");
    }
}

#[cfg(feature = "diff")]
#[test]
fn declared_tuple_diff_ignores_type_ids_and_table_order() {
    use trust_ir::diff::diff;
    let (mut a, _) = observed();
    let elem = a.add_type(Ty::U16).expect("Module::add_type: test fixture");
    let array_tuple = a
        .add_type(Ty::Tuple(vec![Ty::Array(elem, 2), Ty::U8]))
        .expect("Module::add_type: test fixture");
    a.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: array_tuple,
        size: 6,
        align: 2,
        field_offsets: vec![0, 4],
    });
    let mut b = a.clone();
    b.types = vec![
        Ty::Tuple(vec![Ty::Array(TyId::new(2), 2), Ty::U8]),
        a.types[0].clone(),
        Ty::U16,
    ];
    b.tuple_layouts[0].tuple_type = TyId::new(1);
    b.tuple_layouts[1].tuple_type = TyId::new(0);
    b.tuple_layouts.reverse();
    a.validate_tuple_layouts().unwrap();
    b.validate_tuple_layouts().unwrap();
    assert!(diff(&a, &b).is_empty());
    assert_eq!(diff(&a, &b).exit_code(), 0);
    assert!(diff(&a, &b).to_text().is_empty());
}

#[cfg(feature = "diff")]
#[test]
fn declared_tuple_diff_does_not_discard_duplicate_or_malformed_rows() {
    use trust_ir::diff::diff;
    let (a, _) = observed();
    let mut b = a.clone();
    b.tuple_layouts.push(b.tuple_layouts[0].clone());
    assert_eq!(diff(&a, &b).exit_code(), 1);
    let mut cycle = a.clone();
    cycle.types[0] = Ty::Tuple(vec![Ty::Array(TyId::new(0), 1)]);
    cycle.tuple_layouts[0].field_offsets = vec![0];
    assert!(cycle.validate_tuple_layouts().is_err());
    assert_eq!(diff(&a, &cycle).exit_code(), 1);
}

#[cfg(feature = "diff")]
#[test]
fn declared_tuple_diff_handles_recursive_pointer_type_identity() {
    use trust_ir::diff::diff;
    use trust_ir::{FieldDef, StructDef, StructId};
    let make = |id, offset| {
        let mut m = Module::new("recursive_tuple");
        m.target_info = Some(target());
        let id = StructId::new(id);
        let sd = StructDef {
            id,
            name: "Node".into(),
            fields: vec![FieldDef {
                name: "next".into(),
                ty: Ty::PtrConst(Box::new(Ty::Struct(id))),
                offset: Some(offset),
            }],
            size: Some(16),
            align: Some(8),
            repr: Default::default(),
            origin: None,
        };
        m.add_struct(sd);
        let ty = m
            .add_type(Ty::Tuple(vec![Ty::PtrConst(Box::new(Ty::Struct(id)))]))
            .expect("Module::add_type: test fixture");
        m.tuple_layouts.push(TupleLayoutDescriptor {
            tuple_type: ty,
            size: 8,
            align: 8,
            field_offsets: vec![0],
        });
        m.validate_tuple_layouts().unwrap();
        m
    };
    assert!(diff(&make(0, 0), &make(17, 0)).is_empty());
    assert_eq!(diff(&make(0, 0), &make(17, 8)).exit_code(), 1);
}
