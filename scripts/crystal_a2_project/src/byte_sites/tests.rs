// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{byte_ty, reflect, rows_match, run, AUTHORITY};
use trust_ir::constant::Constant;
use trust_ir::inst::Inst;
use trust_ir::ty::{EnumDef, StructDef, StructRepr};
use trust_ir::value::{BlockId, EnumId, FuncId, StructId, TyId, ValueId};
use trust_ir::{Block, FatPtrKind, FuncTy, Function, InstrNode, Module, Ty};

fn module(params: Vec<(u32, Ty)>, body: Vec<InstrNode>) -> Module {
    let mut module = Module::new("byte-diagnostic");
    let signature = module
        .add_func_type(FuncTy {
            params: params.iter().map(|(_, ty)| ty.clone()).collect(),
            returns: Vec::new(),
            is_vararg: false,
            abi: None,
        })
        .expect("add_func_type: test fixture");
    let mut function = Function::new(FuncId::new(71), "sparse", signature, BlockId::new(29));
    let mut block = Block::new(BlockId::new(29));
    block.params = params
        .into_iter()
        .map(|(id, ty)| (ValueId::new(id), ty))
        .collect();
    block.body = body;
    function.blocks.push(block);
    module.functions.push(function);
    module
}

fn copy(operand: u32, result: u32, ty: Ty) -> InstrNode {
    InstrNode::new(Inst::Copy {
        operand: ValueId::new(operand),
        ty,
    })
    .with_result(ValueId::new(result))
}

#[test]
fn byte_sites_sparse_raw_ids_origins_and_authority_remain_explicit() {
    let m = module(vec![(403, Ty::U64)], vec![copy(403, 819, Ty::U64)]);
    let reflected = reflect(&m, FuncId::new(71)).expect("diagnostic census");
    assert_eq!(reflected.function, 71);
    assert_eq!(reflected.blocks, vec![29]);
    assert_eq!(reflected.rows[0].raw.value.0, 403);
    assert_eq!(reflected.rows[1].raw.value.0, 819);
    assert_eq!(reflected.nodes[0].occurrences, vec![403]);
    let json = reflected
        .json("raw.bin", "digest")
        .expect("checked rendering");
    assert!(json.contains(AUTHORITY));
    assert!(json.contains("\"pc\":0,\"result_index\":0"));
    assert!(json.contains("\"param_index\":0"));
    assert!(json.contains("\"raw_ids_preserved\":true"));
}

#[test]
fn byte_sites_same_carrier_nominal_aggregate_ids_and_all_fat_kinds_are_distinct() {
    let mut m = module(
        vec![
            (7, Ty::Struct(StructId::new(11))),
            (8, Ty::Struct(StructId::new(93))),
            (9, Ty::Enum(EnumId::new(11))),
            (10, Ty::Enum(EnumId::new(93))),
        ],
        Vec::new(),
    );
    for id in [11, 93] {
        m.structs.push(StructDef {
            id: StructId::new(id),
            name: format!("S{id}"),
            fields: Vec::new(),
            size: None,
            align: None,
            repr: StructRepr::Rust,
            origin: None,
        });
        m.enums
            .push(EnumDef::new(EnumId::new(id), format!("E{id}"), Vec::new()));
    }
    assert_ne!(
        byte_ty(&m, &Ty::Struct(StructId::new(11))).expect("struct11"),
        byte_ty(&m, &Ty::Struct(StructId::new(93))).expect("struct93")
    );
    assert_ne!(
        byte_ty(&m, &Ty::Enum(EnumId::new(11))).expect("enum11"),
        byte_ty(&m, &Ty::Enum(EnumId::new(93))).expect("enum93")
    );
    let rows = reflect(&m, FuncId::new(71)).expect("raw nominal rows, not layout admission");
    assert_eq!(rows.rows[0].byte_ty, "(IRTy.struct_ 11)");
    assert_eq!(rows.rows[1].byte_ty, "(IRTy.struct_ 93)");
    assert_eq!(rows.rows[2].byte_ty, "(IRTy.enum_ 11)");
    assert_eq!(rows.rows[3].byte_ty, "(IRTy.enum_ 93)");
    m.types.push(Ty::U8);
    let kinds = [
        FatPtrKind::Str,
        FatPtrKind::Slice(TyId::new(0)),
        FatPtrKind::TraitObject { trait_id: 208 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ];
    let images = kinds
        .into_iter()
        .map(|kind| byte_ty(&m, &Ty::FatPtr(kind)).expect("fat image"))
        .collect::<std::collections::BTreeSet<_>>();
    assert_eq!(images.len(), 5);
    assert!(images.contains("IRTy.fatstr_"));
    assert!(images.contains("(IRTy.fatslice_ (IRTy.uint_ 8))"));
    assert!(images.contains("(IRTy.fatdyn_ 208)"));
    assert!(images.contains("IRTy.containerlen_"));
    assert!(images.contains("IRTy.containervtable_"));
}

#[test]
fn byte_sites_duplicate_definitions_blocks_and_module_ids_refuse_before_lookup() {
    let duplicate = module(vec![(7, Ty::Bool)], vec![copy(7, 7, Ty::Bool)]);
    assert!(reflect(&duplicate, FuncId::new(71))
        .expect_err("duplicate SSA")
        .contains("duplicate SSA"));
    let mut duplicate = module(vec![(7, Ty::Bool)], Vec::new());
    duplicate.functions[0]
        .blocks
        .push(Block::new(BlockId::new(29)));
    assert!(reflect(&duplicate, FuncId::new(71))
        .expect_err("duplicate block")
        .contains("duplicate block"));
    let mut duplicate = module(Vec::new(), Vec::new());
    duplicate.functions.push(duplicate.functions[0].clone());
    assert!(reflect(&duplicate, FuncId::new(71))
        .expect_err("duplicate function")
        .contains("duplicate module function"));
    let mut duplicate = module(Vec::new(), Vec::new());
    duplicate
        .enums
        .push(EnumDef::new(EnumId::new(93), "E93", Vec::new()));
    duplicate.enums.push(duplicate.enums[0].clone());
    assert!(reflect(&duplicate, FuncId::new(71))
        .expect_err("duplicate enum")
        .contains("duplicate module enum"));
    let mut duplicate = module(Vec::new(), Vec::new());
    duplicate.structs.push(StructDef {
        id: StructId::new(93),
        name: "S93".into(),
        fields: Vec::new(),
        size: None,
        align: None,
        repr: StructRepr::Rust,
        origin: None,
    });
    duplicate.structs.push(duplicate.structs[0].clone());
    assert!(reflect(&duplicate, FuncId::new(71))
        .expect_err("duplicate struct")
        .contains("duplicate module struct"));
}

#[test]
fn byte_sites_result_arity_and_unresolved_result_calls_refuse_before_zip() {
    let missing = module(
        Vec::new(),
        vec![InstrNode::new(Inst::Const {
            ty: Ty::Bool,
            value: Constant::Bool(false),
        })],
    );
    assert!(reflect(&missing, FuncId::new(71))
        .expect_err("missing result")
        .contains("result arity"));
    let unresolved = module(
        Vec::new(),
        vec![InstrNode::new(Inst::Call {
            callee: FuncId::new(999),
            args: Vec::new(),
        })
        .with_result(ValueId::new(7))
        .with_result(ValueId::new(8))],
    );
    assert!(reflect(&unresolved, FuncId::new(71))
        .expect_err("unresolved results")
        .contains("result arity"));
    let mut duplicate_results = module(
        Vec::new(),
        vec![InstrNode::new(Inst::Call {
            callee: FuncId::new(88),
            args: Vec::new(),
        })
        .with_result(ValueId::new(7))
        .with_result(ValueId::new(7))],
    );
    let sig = duplicate_results
        .add_func_type(FuncTy {
            params: Vec::new(),
            returns: vec![Ty::U64, Ty::Bool],
            is_vararg: false,
            abi: None,
        })
        .expect("add_func_type: test fixture");
    duplicate_results.functions.push(Function::new(
        FuncId::new(88),
        "two-results",
        sig,
        BlockId::new(0),
    ));
    assert!(reflect(&duplicate_results, FuncId::new(71))
        .expect_err("duplicate actual result carriers")
        .contains("duplicate SSA"));
}

#[test]
fn byte_sites_zero_result_call_is_not_promoted_to_resolution_or_validation() {
    let m = module(
        Vec::new(),
        vec![InstrNode::new(Inst::Call {
            callee: FuncId::new(999),
            args: Vec::new(),
        })],
    );
    let diagnostic = reflect(&m, FuncId::new(71))
        .expect("only a row/use census")
        .json("raw.bin", "digest")
        .expect("checked rendering");
    assert!(diagnostic.contains("\"call_resolution_established\":false"));
    assert!(diagnostic.contains("\"module_validation_authority\":false"));
}

#[test]
fn byte_sites_undefined_uses_refuse_but_repeated_occurrences_are_valid() {
    let undefined = module(Vec::new(), vec![copy(999, 7, Ty::Bool)]);
    assert!(reflect(&undefined, FuncId::new(71))
        .expect_err("undefined SSA")
        .contains("undefined SSA use 999"));
    let m = module(
        vec![(7, Ty::Bool)],
        vec![InstrNode::new(Inst::Select {
            cond: ValueId::new(7),
            then_val: ValueId::new(7),
            else_val: ValueId::new(7),
            ty: Ty::Bool,
        })
        .with_result(ValueId::new(99))],
    );
    let result = reflect(&m, FuncId::new(71)).expect("repeated valid use");
    assert_eq!(result.nodes[0].occurrences, vec![7, 7, 7]);
    assert_eq!(result.nodes[0].operands, vec![7]);
}

#[test]
fn byte_sites_canonical_visitor_censuses_branch_call_return_and_dialect_uses() {
    let nodes =
        vec![
            Inst::Br {
                target: BlockId::new(29),
                args: vec![ValueId::new(7), ValueId::new(8)],
            },
            Inst::CondBr {
                cond: ValueId::new(7),
                then_target: BlockId::new(29),
                then_args: vec![ValueId::new(8)],
                else_target: BlockId::new(29),
                else_args: vec![ValueId::new(7)],
            },
            Inst::Call {
                callee: FuncId::new(999),
                args: vec![ValueId::new(8), ValueId::new(7)],
            },
            Inst::Return {
                values: vec![ValueId::new(8), ValueId::new(7)],
            },
            Inst::DialectOp(Box::new(
                trust_ir::dialect::inst::DialectInst::new("diagnostic", "unknown-op")
                    .with_operands([ValueId::new(7), ValueId::new(8), ValueId::new(7)]),
            )),
        ];
    let m = module(
        vec![(7, Ty::Bool), (8, Ty::U64)],
        nodes.into_iter().map(InstrNode::new).collect(),
    );
    let census = reflect(&m, FuncId::new(71)).expect("visitor census, not CFG/dialect validation");
    assert_eq!(
        census
            .nodes
            .iter()
            .map(|node| node.occurrences.clone())
            .collect::<Vec<_>>(),
        vec![
            vec![7, 8],
            vec![7, 8, 7],
            vec![8, 7],
            vec![8, 7],
            vec![7, 8, 7]
        ]
    );
    assert_eq!(census.nodes[4].operands, vec![7, 8]);
    let json = census.json("raw.bin", "digest").expect("checked rendering");
    assert!(json.contains("\"operand_occurrence_count\":12"));
    assert!(json.contains("\"deduplicated_operand_row_count\":10"));
    assert!(json.contains("\"instruction_typing_established\":false"));
}

#[test]
fn byte_sites_valid_cyclic_unresolved_borrows_all_refuse_and_missing_result_is_arity() {
    for (params, operand, result) in [
        (vec![(7, Ty::Ptr)], 7, 99),
        (vec![(7, Ty::FatPtr(FatPtrKind::Str))], 7, 99),
        (Vec::new(), 99, 99),
        (Vec::new(), 999, 99),
    ] {
        let m = module(
            params,
            vec![InstrNode::new(Inst::Borrow {
                ptr: ValueId::new(operand),
            })
            .with_result(ValueId::new(result))],
        );
        assert!(reflect(&m, FuncId::new(71))
            .expect_err("borrow unsupported")
            .contains("unsupported Borrow/BorrowMut"));
    }
    let malformed = module(
        Vec::new(),
        vec![InstrNode::new(Inst::BorrowMut {
            ptr: ValueId::new(999),
        })],
    );
    assert!(reflect(&malformed, FuncId::new(71))
        .expect_err("zero result borrow")
        .contains("result arity"));
}

#[test]
fn byte_sites_unsupported_types_are_not_erased_and_slice_resolution_is_bounded() {
    let m = module(Vec::new(), Vec::new());
    let unsupported = [
        Ty::Ref(Box::new(Ty::Ptr)),
        Ty::RefMut(Box::new(Ty::Ptr)),
        Ty::PtrConst(Box::new(Ty::Bool)),
        Ty::PtrMut(Box::new(Ty::Bool)),
        Ty::Rc(Box::new(Ty::Bool)),
        Ty::Tuple(vec![Ty::Bool]),
        Ty::Usize,
        Ty::Isize,
        Ty::Char,
        Ty::Refine(TyId::new(0), trust_ir::PredId::new(0)),
    ];
    for ty in unsupported {
        assert!(byte_ty(&m, &ty)
            .expect_err("unsupported exact type")
            .contains("no erasure"));
        let rows = module(vec![(7, ty)], Vec::new());
        assert!(reflect(&rows, FuncId::new(71)).is_err());
    }
    let missing = Ty::FatPtr(FatPtrKind::Slice(TyId::new(42)));
    assert!(byte_ty(&m, &missing)
        .expect_err("missing slice type")
        .contains("missing slice"));
    let mut cyclic = m;
    cyclic
        .types
        .push(Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))));
    assert!(byte_ty(&cyclic, &cyclic.types[0])
        .expect_err("cyclic slice type")
        .contains("cyclic slice"));
    let mut deep = module(Vec::new(), Vec::new());
    for index in 0..65 {
        deep.types
            .push(Ty::FatPtr(FatPtrKind::Slice(TyId::new(index + 1))));
    }
    deep.types.push(Ty::Bool);
    assert!(byte_ty(&deep, &deep.types[0])
        .expect_err("bounded depth")
        .contains("depth limit"));
}

#[test]
fn byte_sites_cli_requires_exact_mode_and_numeric_id_without_legacy_flags() {
    for args in [
        vec!["--byte-sites", "raw.bin"],
        vec!["--byte-sites", "raw.bin", "-1"],
        vec!["--byte-sites", "raw.bin", "+1"],
        vec!["--byte-sites", "raw.bin", "1", "--with", "other"],
    ] {
        assert!(run(&args.into_iter().map(str::to_owned).collect::<Vec<_>>()).is_err());
    }
}

#[test]
fn byte_sites_ordered_full_row_comparison_preserves_every_metadata_field() {
    use trust_ir::bridge::{TypedValueMetadata, ValueMetadataOrigin};
    use trust_ir::{ProofAnnotation, SourceSpan};
    let instruction = TypedValueMetadata {
        value: ValueId::new(7),
        ty: Ty::U64,
        origin: ValueMetadataOrigin::InstrResult {
            block: BlockId::new(29),
            instruction_index: 3,
            result_index: 1,
        },
        proofs: vec![ProofAnnotation::Aligned(8), ProofAnnotation::Aligned(16)],
        span: Some(SourceSpan {
            file: 3,
            line: 9,
            col: 11,
        }),
    };
    let parameter = TypedValueMetadata {
        value: ValueId::new(8),
        ty: Ty::Bool,
        origin: ValueMetadataOrigin::BlockParam {
            block: BlockId::new(29),
            param_index: 0,
        },
        proofs: Vec::new(),
        span: None,
    };
    let baseline = vec![instruction.clone(), parameter.clone()];
    assert!(rows_match(&baseline, &baseline.clone()));
    assert!(!rows_match(&baseline, &[]));
    assert!(!rows_match(&baseline, &baseline[..1]));
    assert!(!rows_match(
        &baseline,
        &[parameter.clone(), instruction.clone()]
    ));
    let mut changed = instruction.clone();
    changed.value = ValueId::new(99);
    assert!(!rows_match(&baseline, &[changed, parameter.clone()]));
    let mut changed = instruction.clone();
    changed.ty = Ty::U32;
    assert!(!rows_match(&baseline, &[changed, parameter.clone()]));
    for origin in [
        ValueMetadataOrigin::InstrResult {
            block: BlockId::new(30),
            instruction_index: 3,
            result_index: 1,
        },
        ValueMetadataOrigin::InstrResult {
            block: BlockId::new(29),
            instruction_index: 4,
            result_index: 1,
        },
        ValueMetadataOrigin::InstrResult {
            block: BlockId::new(29),
            instruction_index: 3,
            result_index: 2,
        },
        ValueMetadataOrigin::BlockParam {
            block: BlockId::new(29),
            param_index: 0,
        },
    ] {
        let mut changed = instruction.clone();
        changed.origin = origin;
        assert!(!rows_match(&baseline, &[changed, parameter.clone()]));
    }
    for origin in [
        ValueMetadataOrigin::BlockParam {
            block: BlockId::new(30),
            param_index: 0,
        },
        ValueMetadataOrigin::BlockParam {
            block: BlockId::new(29),
            param_index: 1,
        },
        ValueMetadataOrigin::InstrResult {
            block: BlockId::new(29),
            instruction_index: 0,
            result_index: 0,
        },
    ] {
        let mut changed = parameter.clone();
        changed.origin = origin;
        assert!(!rows_match(&baseline, &[instruction.clone(), changed]));
    }
    let mut changed = instruction.clone();
    changed.proofs.reverse();
    assert!(!rows_match(&baseline, &[changed, parameter.clone()]));
    let mut changed = instruction.clone();
    changed.proofs.clear();
    assert!(!rows_match(&baseline, &[changed, parameter.clone()]));
    for span in [
        None,
        Some(SourceSpan {
            file: 4,
            line: 9,
            col: 11,
        }),
        Some(SourceSpan {
            file: 3,
            line: 10,
            col: 11,
        }),
        Some(SourceSpan {
            file: 3,
            line: 9,
            col: 12,
        }),
    ] {
        let mut changed = instruction.clone();
        changed.span = span;
        assert!(!rows_match(&baseline, &[changed, parameter.clone()]));
    }
}

#[test]
fn byte_sites_exact_type_variant_pairs_name_all_compiled_variants() {
    use trust_ir::ty::{DialectTy, HandleTy, SetRepr};
    use trust_ir::value::{ClosureTyId, FuncTyId, PredId, RecordId};
    let cases = vec![
        Ty::I8,
        Ty::I16,
        Ty::I32,
        Ty::I64,
        Ty::I128,
        Ty::U8,
        Ty::U16,
        Ty::U32,
        Ty::U64,
        Ty::U128,
        Ty::Isize,
        Ty::Usize,
        Ty::Char,
        Ty::Error,
        Ty::F16,
        Ty::F32,
        Ty::F64,
        Ty::Bool,
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
        Ty::Vector(Box::new(Ty::U16), 4),
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(7))),
        Ty::Struct(StructId::new(11)),
        Ty::Array(TyId::new(12), 9),
        Ty::Tuple(vec![Ty::Bool, Ty::U64]),
        Ty::Enum(EnumId::new(13)),
        Ty::Func(FuncTyId::new(14)),
        Ty::FnItem(FuncId::new(14)),
        Ty::Ref(Box::new(Ty::Bool)),
        Ty::RefMut(Box::new(Ty::Bool)),
        Ty::PtrConst(Box::new(Ty::Bool)),
        Ty::PtrMut(Box::new(Ty::Bool)),
        Ty::Rc(Box::new(Ty::Bool)),
        Ty::Set(TyId::new(15), SetRepr::Bitset),
        Ty::Sequence(TyId::new(16)),
        Ty::Record(RecordId::new(17)),
        Ty::Closure(ClosureTyId::new(18)),
        Ty::Refine(TyId::new(19), PredId::new(20)),
        Ty::Dialect(Box::new(DialectTy::new("space", "name", 1))),
        Ty::Handle(Box::new(HandleTy::new("Nat", "runtime::Nat"))),
        Ty::Storage(trust_ir::StorageLayout::new(8, 8)),
    ];
    let storage = Ty::Storage(trust_ir::StorageLayout::new(8, 8));
    assert!(byte_ty(&Module::new("storage"), &storage)
        .unwrap_err()
        .contains("no erasure"));
    assert_eq!(cases.len(), 42);
    for (i, a) in cases.iter().enumerate() {
        for (j, b) in cases.iter().enumerate() {
            assert_eq!(
                super::metadata_eq::ty_matches(a, b),
                i == j,
                "raw type variant pair {i}/{j}"
            );
        }
    }
}

#[test]
fn byte_sites_exact_type_payloads_recurse_without_resolving_raw_ids() {
    use trust_ir::ty::{DialectTy, HandleTy, SetRepr};
    use trust_ir::value::{ClosureTyId, FuncTyId, PredId, RecordId};
    let changes = vec![
        (
            Ty::Vector(Box::new(Ty::Bool), 4),
            Ty::Vector(Box::new(Ty::U64), 4),
        ),
        (
            Ty::Vector(Box::new(Ty::Bool), 4),
            Ty::Vector(Box::new(Ty::Bool), 8),
        ),
        (
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(7))),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(8))),
        ),
        (
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 7 }),
            Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 8 }),
        ),
        (Ty::Struct(StructId::new(7)), Ty::Struct(StructId::new(8))),
        (Ty::Array(TyId::new(7), 3), Ty::Array(TyId::new(8), 3)),
        (Ty::Array(TyId::new(7), 3), Ty::Array(TyId::new(7), 4)),
        (
            Ty::Tuple(vec![Ty::Bool, Ty::U64]),
            Ty::Tuple(vec![Ty::U64, Ty::Bool]),
        ),
        (
            Ty::Tuple(vec![Ty::Bool]),
            Ty::Tuple(vec![Ty::Bool, Ty::Bool]),
        ),
        (Ty::Tuple(vec![Ty::Bool]), Ty::Tuple(vec![Ty::U64])),
        (Ty::Enum(EnumId::new(7)), Ty::Enum(EnumId::new(8))),
        (Ty::Func(FuncTyId::new(7)), Ty::Func(FuncTyId::new(8))),
        (Ty::FnItem(FuncId::new(7)), Ty::FnItem(FuncId::new(8))),
        (Ty::Ref(Box::new(Ty::Bool)), Ty::Ref(Box::new(Ty::U64))),
        (
            Ty::RefMut(Box::new(Ty::Bool)),
            Ty::RefMut(Box::new(Ty::U64)),
        ),
        (
            Ty::PtrConst(Box::new(Ty::Bool)),
            Ty::PtrConst(Box::new(Ty::U64)),
        ),
        (
            Ty::PtrMut(Box::new(Ty::Bool)),
            Ty::PtrMut(Box::new(Ty::U64)),
        ),
        (Ty::Rc(Box::new(Ty::Bool)), Ty::Rc(Box::new(Ty::U64))),
        (
            Ty::Set(TyId::new(7), SetRepr::Bitset),
            Ty::Set(TyId::new(8), SetRepr::Bitset),
        ),
        (
            Ty::Set(TyId::new(7), SetRepr::Bitset),
            Ty::Set(TyId::new(7), SetRepr::Boxed),
        ),
        (Ty::Sequence(TyId::new(7)), Ty::Sequence(TyId::new(8))),
        (Ty::Record(RecordId::new(7)), Ty::Record(RecordId::new(8))),
        (
            Ty::Closure(ClosureTyId::new(7)),
            Ty::Closure(ClosureTyId::new(8)),
        ),
        (
            Ty::Refine(TyId::new(7), PredId::new(3)),
            Ty::Refine(TyId::new(8), PredId::new(3)),
        ),
        (
            Ty::Refine(TyId::new(7), PredId::new(3)),
            Ty::Refine(TyId::new(7), PredId::new(4)),
        ),
        (
            Ty::Dialect(Box::new(DialectTy::new("a", "b", 1))),
            Ty::Dialect(Box::new(DialectTy::new("c", "b", 1))),
        ),
        (
            Ty::Dialect(Box::new(DialectTy::new("a", "b", 1))),
            Ty::Dialect(Box::new(DialectTy::new("a", "c", 1))),
        ),
        (
            Ty::Dialect(Box::new(DialectTy::new("a", "b", 1))),
            Ty::Dialect(Box::new(DialectTy::new("a", "b", 2))),
        ),
        (
            Ty::Handle(Box::new(HandleTy::new("Nat", "runtime::Nat"))),
            Ty::Handle(Box::new(HandleTy::new("Int", "runtime::Nat"))),
        ),
        (
            Ty::Handle(Box::new(HandleTy::new("Nat", "runtime::Nat"))),
            Ty::Handle(Box::new(HandleTy::new("Nat", "runtime::Other"))),
        ),
        (
            Ty::Storage(trust_ir::StorageLayout::new(8, 8)),
            Ty::Storage(trust_ir::StorageLayout::new(16, 8)),
        ),
        (
            Ty::Storage(trust_ir::StorageLayout::new(16, 8)),
            Ty::Storage(trust_ir::StorageLayout::new(16, 16)),
        ),
    ];
    assert_eq!(changes.len(), 32);
    for (a, b) in changes {
        assert!(!super::metadata_eq::ty_matches(&a, &b));
        assert!(!super::metadata_eq::ty_matches(&b, &a));
    }
    let nested = Ty::Ref(Box::new(Ty::Tuple(vec![
        Ty::Vector(
            Box::new(Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 93 })),
            2,
        ),
        Ty::Rc(Box::new(Ty::Struct(StructId::new(81)))),
    ])));
    assert!(super::metadata_eq::ty_matches(&nested, &nested.clone()));
    let changed = Ty::Ref(Box::new(Ty::Tuple(vec![
        Ty::Vector(
            Box::new(Ty::FatPtr(FatPtrKind::TraitObject { trait_id: 94 })),
            2,
        ),
        Ty::Rc(Box::new(Ty::Struct(StructId::new(81)))),
    ])));
    assert!(!super::metadata_eq::ty_matches(&nested, &changed));
}

#[test]
fn byte_sites_exact_proof_variant_pairs_payloads_order_and_float_semantics() {
    use trust_ir::inst::Ordering;
    use trust_ir::proof::Divergence;
    use trust_ir::value::{ProofId, ProofTag};
    use trust_ir::ProofAnnotation as P;
    let cases = vec![
        P::InBounds,
        P::NotNull,
        P::ValidBorrow,
        P::UniqueBorrow,
        P::SharedBorrow,
        P::ValidDealloc,
        P::NoOverflow,
        P::NoWrap,
        P::DivNonZero,
        P::ShiftInRange,
        P::Wrapping,
        P::Pure,
        P::Terminates,
        P::Deterministic,
        P::Associative,
        P::Commutative,
        P::DataRaceFree,
        P::Monotonic,
        P::NoAlias,
        P::NoPanic,
        P::NoUndef,
        P::Tainted,
        P::TrustedSink,
        P::ReadonlyTable,
        P::AppendOnlyBuffer,
        P::AtomicSetInsert,
        P::ParallelMap,
        P::FreshSymbolicHavoc,
        P::RegionHavocStore,
        P::AtomicOrdering(Ordering::Relaxed),
        P::BoundedOutput { lo: 1.0, hi: 2.0 },
        P::Aligned(8),
        P::BoundedLoop(9),
        P::DivergenceClass(Divergence::Low),
        P::Custom(ProofTag::new(10)),
        P::ProofRef(ProofId::new(11)),
        P::ValueRange { lo: -12, hi: 13 },
        P::KnownBits { zeros: 2, ones: 1 },
        P::BranchWeights(vec![3, 4]),
    ];
    assert_eq!(cases.len(), 39);
    for (i, a) in cases.iter().enumerate() {
        for (j, b) in cases.iter().enumerate() {
            assert_eq!(
                super::metadata_eq::proof_matches(a, b),
                i == j,
                "annotation variant pair {i}/{j}"
            );
        }
    }
    let changes = vec![
        (
            P::AtomicOrdering(Ordering::Relaxed),
            P::AtomicOrdering(Ordering::Acquire),
        ),
        (
            P::BoundedOutput { lo: 1.0, hi: 2.0 },
            P::BoundedOutput { lo: 0.0, hi: 2.0 },
        ),
        (
            P::BoundedOutput { lo: 1.0, hi: 2.0 },
            P::BoundedOutput { lo: 1.0, hi: 3.0 },
        ),
        (P::Aligned(8), P::Aligned(16)),
        (P::BoundedLoop(9), P::BoundedLoop(10)),
        (
            P::DivergenceClass(Divergence::Low),
            P::DivergenceClass(Divergence::High),
        ),
        (P::Custom(ProofTag::new(10)), P::Custom(ProofTag::new(11))),
        (P::ProofRef(ProofId::new(11)), P::ProofRef(ProofId::new(12))),
        (
            P::ValueRange { lo: -12, hi: 13 },
            P::ValueRange { lo: -11, hi: 13 },
        ),
        (
            P::ValueRange { lo: -12, hi: 13 },
            P::ValueRange { lo: -12, hi: 14 },
        ),
        (
            P::KnownBits { zeros: 2, ones: 1 },
            P::KnownBits { zeros: 4, ones: 1 },
        ),
        (
            P::KnownBits { zeros: 2, ones: 1 },
            P::KnownBits { zeros: 2, ones: 4 },
        ),
        (P::BranchWeights(vec![3, 4]), P::BranchWeights(vec![4, 3])),
        (P::BranchWeights(vec![3, 4]), P::BranchWeights(vec![3])),
        (P::BranchWeights(vec![3, 4]), P::BranchWeights(vec![3, 5])),
    ];
    assert_eq!(changes.len(), 15);
    for (a, b) in changes {
        assert!(!super::metadata_eq::proof_matches(&a, &b));
        assert!(!super::metadata_eq::proof_matches(&b, &a));
    }
    let a = vec![P::Aligned(8), P::Aligned(16)];
    assert!(super::metadata_eq::proofs_match(&a, &a.clone()));
    assert!(!super::metadata_eq::proofs_match(
        &a,
        &[P::Aligned(16), P::Aligned(8)]
    ));
    assert!(!super::metadata_eq::proofs_match(&a, &[P::Aligned(8)]));
    let nan_lo = P::BoundedOutput {
        lo: f64::NAN,
        hi: 2.0,
    };
    let nan_hi = P::BoundedOutput {
        lo: 1.0,
        hi: f64::NAN,
    };
    assert!(!super::metadata_eq::proof_matches(&nan_lo, &nan_lo));
    assert!(!super::metadata_eq::proof_matches(&nan_hi, &nan_hi));
    assert!(super::metadata_eq::proof_matches(
        &P::BoundedOutput { lo: -0.0, hi: 0.0 },
        &P::BoundedOutput { lo: 0.0, hi: -0.0 },
    ));
}

#[test]
fn byte_sites_exact_nested_enum_families_classify_all_variant_pairs() {
    use trust_ir::inst::Ordering;
    use trust_ir::proof::Divergence;
    use trust_ir::ty::SetRepr;
    let fat = [
        FatPtrKind::Slice(TyId::new(7)),
        FatPtrKind::Str,
        FatPtrKind::TraitObject { trait_id: 8 },
        FatPtrKind::ContainerLen,
        FatPtrKind::ContainerVtable,
    ];
    let set = [SetRepr::Bitset, SetRepr::Boxed];
    let order = [
        Ordering::Relaxed,
        Ordering::Acquire,
        Ordering::Release,
        Ordering::AcqRel,
        Ordering::SeqCst,
    ];
    let divergence = [Divergence::Uniform, Divergence::Low, Divergence::High];
    for (i, a) in fat.iter().enumerate() {
        for (j, b) in fat.iter().enumerate() {
            assert_eq!(super::metadata_eq::fat_matches(a, b), i == j);
        }
    }
    for (i, a) in set.iter().enumerate() {
        for (j, b) in set.iter().enumerate() {
            assert_eq!(super::metadata_eq::set_matches(a, b), i == j);
        }
    }
    for (i, a) in order.iter().enumerate() {
        for (j, b) in order.iter().enumerate() {
            assert_eq!(super::metadata_eq::ordering_matches(a, b), i == j);
        }
    }
    for (i, a) in divergence.iter().enumerate() {
        for (j, b) in divergence.iter().enumerate() {
            assert_eq!(super::metadata_eq::divergence_matches(a, b), i == j);
        }
    }
}

#[test]
fn byte_sites_nominal_function_items_are_not_structural_function_carriers() {
    let mut m = module(Vec::new(), Vec::new());
    let signature = m
        .add_func_type(FuncTy {
            params: vec![Ty::U64],
            returns: vec![Ty::U64],
            is_vararg: false,
            abi: None,
        })
        .expect("structural function signature");
    assert_eq!(
        byte_ty(&m, &Ty::Func(signature)).unwrap(),
        format!("(IRTy.func_ {})", signature.0)
    );
    assert_eq!(byte_ty(&m, &Ty::U64).unwrap(), "(IRTy.uint_ 64)");

    // Name a separate resident scalar identity, so refusal cannot be credited to
    // a missing target or a recursively defined function-item signature.
    let mut target = Function::new(
        FuncId::new(72),
        "nominal-target",
        signature,
        BlockId::new(0),
    );
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::U64));
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    target.blocks.push(block);
    m.functions.push(target);
    let nominal = Ty::FnItem(FuncId::new(72));
    let refusal = byte_ty(&m, &nominal).expect_err("nominal function item has no ByteTy image");
    assert!(refusal.contains("FnItem"), "{refusal}");
    assert!(refusal.contains("no erasure"), "{refusal}");
    m.func_types[0].params = vec![nominal.clone()];
    m.functions[0].blocks[0].params = vec![(ValueId::new(403), nominal)];
    let refusal = reflect(&m, FuncId::new(71)).expect_err("actual metadata row must refuse");
    assert!(refusal.contains("FnItem"), "{refusal}");
    assert!(refusal.contains("no erasure"), "{refusal}");
}
