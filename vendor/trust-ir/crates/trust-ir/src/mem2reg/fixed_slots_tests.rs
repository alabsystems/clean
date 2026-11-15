// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{promote_allocas_function, promote_allocas_module};
use crate::proof::{
    ClauseBinding, ClausePlace, ClauseSort, ObligationKind, ProofAnnotation, ProofFormula,
    ProofObligation, ProofStatus,
};
use crate::value::{BlockId, FuncId, FuncTyId, ProofId};
use crate::{
    Block, BodyGate, CastOp, Constant, Endianness, FuncTy, Function, Inst, InstrNode,
    InterpretValue, Interpreter, Module, TargetInfo, Ty, ValueId,
};

struct Fixture {
    function: Function,
    next: u32,
}

impl Fixture {
    fn new() -> Self {
        let mut function =
            Function::new(FuncId::new(0), "fixed", FuncTyId::new(0), BlockId::new(0));
        function.blocks.push(Block::new(BlockId::new(0)));
        Self { function, next: 0 }
    }

    fn emit(&mut self, inst: Inst) -> ValueId {
        let value = ValueId::new(self.next);
        self.next += 1;
        self.function.blocks[0]
            .body
            .push(InstrNode::new(inst).with_result(value));
        value
    }

    fn effect(&mut self, inst: Inst) {
        self.function.blocks[0].body.push(InstrNode::new(inst));
    }

    fn integer(&mut self, ty: Ty, value: i128) -> ValueId {
        self.emit(Inst::Const {
            ty,
            value: Constant::Int(value),
        })
    }

    fn array(&mut self, ty: Ty, count: i128) -> ValueId {
        let count = self.integer(Ty::U64, count);
        self.emit(Inst::Alloca {
            ty,
            count: Some(count),
            align: None,
        })
    }

    fn gep(&mut self, ty: Ty, base: ValueId, slots: &[i128]) -> ValueId {
        let indices = slots
            .iter()
            .map(|slot| self.integer(Ty::I64, *slot))
            .collect();
        self.emit(Inst::GEP {
            pointee_ty: ty,
            base,
            indices,
            inbounds: false,
        })
    }

    fn store(&mut self, ty: Ty, ptr: ValueId, value: ValueId) {
        self.effect(Inst::Store {
            ty,
            ptr,
            value,
            volatile: false,
            align: None,
        });
    }

    fn load(&mut self, ty: Ty, ptr: ValueId) -> ValueId {
        self.emit(Inst::Load {
            ty,
            ptr,
            volatile: false,
            align: None,
        })
    }

    fn finish(mut self, returns: &[(ValueId, Ty)]) -> Module {
        self.effect(Inst::Return {
            values: returns.iter().map(|(value, _)| *value).collect(),
        });
        let mut module = Module::new("fixed-slots");
        module
            .add_func_type(FuncTy {
                params: vec![],
                returns: returns.iter().map(|(_, ty)| ty.clone()).collect(),
                abi: None,
                is_vararg: false,
            })
            .expect("Module::add_func_type: test fixture");
        module.functions.push(self.function);
        module
    }
}

fn simple() -> (Module, ValueId, ValueId, ValueId) {
    let mut f = Fixture::new();
    let root = f.array(Ty::I64, 2);
    let ptr = f.gep(Ty::I64, root, &[1]);
    let value = f.integer(Ty::I64, 19);
    f.store(Ty::I64, ptr, value);
    let loaded = f.load(Ty::I64, ptr);
    (f.finish(&[(loaded, Ty::I64)]), root, ptr, loaded)
}

fn run(module: &Module) -> Vec<InterpretValue> {
    Interpreter::with_module(module)
        .execute_func(FuncId::new(0), [])
        .unwrap()
        .returns
}

fn assert_refused(mut module: Module) {
    let before = module.clone();
    promote_allocas_module(&mut module);
    assert_eq!(module, before);
}

#[test]
fn fixed_slots_preserve_source_snapshot_across_real_external_mutation() {
    let mut f = Fixture::new();
    let source = f.array(Ty::I64, 2);
    let source0 = f.gep(Ty::I64, source, &[0]);
    let source1 = f.gep(Ty::I64, source, &[1]);
    let seven = f.integer(Ty::I64, 7);
    let eleven = f.integer(Ty::I64, 11);
    f.store(Ty::I64, source0, seven);
    f.store(Ty::I64, source1, eleven);
    let destination = f.array(Ty::I64, 2);
    let dest0 = f.gep(Ty::I64, destination, &[0]);
    let dest1 = f.gep(Ty::I64, destination, &[1]);
    let first = f.load(Ty::I64, source0);
    f.store(Ty::I64, dest0, first);
    let second = f.load(Ty::I64, source1);
    f.store(Ty::I64, dest1, second);
    f.effect(Inst::Call {
        callee: FuncId::new(1),
        args: vec![source],
    });
    let a = f.load(Ty::I64, dest0);
    let b = f.load(Ty::I64, dest1);
    let changed = f.load(Ty::I64, source0);
    let mut module = f.finish(&[(a, Ty::I64), (b, Ty::I64), (changed, Ty::I64)]);
    let signature = module
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr],
            returns: vec![],
            abi: None,
            is_vararg: false,
        })
        .expect("Module::add_func_type: test fixture");
    let mut helper = Function::new(FuncId::new(1), "mutate-source", signature, BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.params.push((ValueId::new(0), Ty::Ptr));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(100),
        })
        .with_result(ValueId::new(1)),
    );
    block.body.push(InstrNode::new(Inst::Store {
        ty: Ty::I64,
        ptr: ValueId::new(0),
        value: ValueId::new(1),
        volatile: false,
        align: None,
    }));
    block
        .body
        .push(InstrNode::new(Inst::Return { values: vec![] }));
    helper.blocks.push(block);
    module.functions.push(helper);
    let expected = vec![7, 11, 100]
        .into_iter()
        .map(|n| InterpretValue::int(Ty::I64, n).unwrap())
        .collect::<Vec<_>>();
    assert_eq!(run(&module), expected);
    let before = module.functions[0].blocks[0].body.clone();
    promote_allocas_module(&mut module);
    assert_eq!(run(&module), expected);
    let after = &module.functions[0].blocks[0].body;
    // One destination alloca, two address defs, two stores, two loads. Source
    // loads and the actual mutating call are retained at their original order.
    assert_eq!(before.len() - after.len(), 7);
    for value in [first, second, changed] {
        assert_eq!(
            after.iter().find(|node| node.results.contains(&value)),
            before.iter().find(|node| node.results.contains(&value))
        );
    }
    assert_eq!(
        after
            .iter()
            .filter(|node| matches!(node.inst, Inst::Load { .. }))
            .count(),
        3
    );
    let once = module.clone();
    promote_allocas_module(&mut module);
    assert_eq!(module, once);
}

#[test]
fn fixed_slots_follow_exact_copy_and_summed_chained_element_offsets() {
    let mut f = Fixture::new();
    let root = f.array(Ty::I64, 4);
    let two = f.gep(Ty::I64, root, &[1, 1]);
    let copy = f.emit(Inst::Copy {
        ty: Ty::Ptr,
        operand: two,
    });
    let three = f.gep(Ty::I64, copy, &[1]);
    let a = f.integer(Ty::I64, 17);
    let b = f.integer(Ty::I64, 29);
    f.store(Ty::I64, two, a);
    f.store(Ty::I64, three, b);
    let x = f.load(Ty::I64, copy);
    f.store(Ty::I64, copy, b);
    let y = f.load(Ty::I64, two);
    let z = f.load(Ty::I64, three);
    let mut module = f.finish(&[(x, Ty::I64), (y, Ty::I64), (z, Ty::I64)]);
    let before = run(&module);
    promote_allocas_module(&mut module);
    assert_eq!(run(&module), before);
    assert_eq!(
        before,
        [17, 29, 29].map(|n| InterpretValue::int(Ty::I64, n).unwrap())
    );
    assert!(
        module.functions[0].blocks[0]
            .body
            .iter()
            .all(|node| !matches!(
                node.inst,
                Inst::Alloca { .. }
                    | Inst::GEP { .. }
                    | Inst::Copy { ty: Ty::Ptr, .. }
                    | Inst::Load { .. }
                    | Inst::Store { .. }
            ))
    );
}

#[test]
fn fixed_slots_scalar_register_forwarding_exposes_only_dead_integer_addresses() {
    let (mut module, root, _, _) = simple();
    let body = &mut module.functions[0].blocks[0].body;
    let end = body.len() - 1;
    body.splice(
        end..end,
        [
            InstrNode::new(Inst::Alloca {
                ty: Ty::I64,
                count: None,
                align: None,
            })
            .with_result(ValueId::new(80)),
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: root,
            })
            .with_result(ValueId::new(81)),
            InstrNode::new(Inst::Store {
                ty: Ty::I64,
                ptr: ValueId::new(80),
                value: ValueId::new(81),
                volatile: false,
                align: None,
            }),
        ],
    );
    let before = run(&module);
    promote_allocas_module(&mut module);
    assert_eq!(run(&module), before);
    assert!(
        module.functions[0].blocks[0]
            .body
            .iter()
            .all(|node| !matches!(
                node.inst,
                Inst::Alloca { .. }
                    | Inst::Cast {
                        op: CastOp::PtrToInt,
                        ..
                    }
            ))
    );

    let (mut module, root, _, _) = simple();
    let body = &mut module.functions[0].blocks[0].body;
    let end = body.len() - 1;
    body.splice(
        end..end,
        [
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: root,
            })
            .with_result(ValueId::new(81)),
            InstrNode::new(Inst::Cast {
                op: CastOp::IntToPtr,
                src_ty: Ty::I64,
                dst_ty: Ty::Ptr,
                operand: ValueId::new(81),
            })
            .with_result(ValueId::new(82)),
        ],
    );
    // Even an otherwise unused roundtrip gives the integer address an actual
    // user. This is deliberately NOT a pointer-alias reconstruction pass.
    assert_refused(module);
}

#[test]
fn fixed_slots_sparse_large_count_does_not_size_analysis_storage() {
    let mut f = Fixture::new();
    let root = f.array(Ty::I64, 1i128 << 40);
    let ptr = f.gep(Ty::I64, root, &[(1i128 << 40) - 1]);
    let value = f.integer(Ty::I64, 5);
    f.store(Ty::I64, ptr, value);
    let loaded = f.load(Ty::I64, ptr);
    let mut module = f.finish(&[(loaded, Ty::I64)]);
    let before_len = module.functions[0].blocks[0].body.len();
    promote_allocas_module(&mut module);
    assert_eq!(before_len - module.functions[0].blocks[0].body.len(), 4);
    // Only the transformed, allocation-free program is interpreted. The
    // original's enormous allocation is not a workload or memory benchmark.
    assert_eq!(run(&module), vec![InterpretValue::int(Ty::I64, 5).unwrap()]);
}

#[test]
fn fixed_slots_reject_invalid_counts_offsets_types_and_alignment() {
    for count in [-1, 0, i128::from(u64::MAX)] {
        let (mut module, _, _, _) = simple();
        let Inst::Const { value, .. } = &mut module.functions[0].blocks[0].body[0].inst else {
            unreachable!()
        };
        *value = Constant::Int(count);
        assert_refused(module);
    }
    for offset in [-1, 2, i128::MAX] {
        let (mut module, _, _, _) = simple();
        let Inst::Const { value, .. } = &mut module.functions[0].blocks[0].body[2].inst else {
            unreachable!()
        };
        *value = Constant::Int(offset);
        assert_refused(module);
    }
    for mode in 0..7 {
        let (mut module, _, _, _) = simple();
        for node in &mut module.functions[0].blocks[0].body {
            match &mut node.inst {
                Inst::GEP { pointee_ty, .. } if mode == 0 => *pointee_ty = Ty::I8,
                Inst::Load { ty, .. } if mode == 1 => *ty = Ty::U64,
                Inst::Store { ty, .. } if mode == 2 => *ty = Ty::I32,
                Inst::Const {
                    ty,
                    value: Constant::Int(19),
                } if mode == 3 => *ty = Ty::F64,
                Inst::Load { align, .. } if mode == 4 => *align = Some(16),
                Inst::Alloca { align, .. } if mode == 5 => *align = Some(1),
                Inst::Store { align, .. } if mode == 6 => *align = Some(3),
                _ => {}
            }
        }
        assert_refused(module);
    }
}

#[test]
fn fixed_slots_late_escape_and_observable_access_discard_provisional_forwarding() {
    for mode in 0..5 {
        let (mut module, root, ptr, loaded) = simple();
        let body = &mut module.functions[0].blocks[0].body;
        let end = body.len() - 1;
        let inst = match mode {
            0 => Inst::Call {
                callee: FuncId::new(1),
                args: vec![root],
            },
            1 => Inst::Store {
                ty: Ty::I64,
                ptr,
                value: loaded,
                volatile: true,
                align: None,
            },
            2 => Inst::AtomicStore {
                ty: Ty::I64,
                ptr,
                value: loaded,
                ordering: crate::Ordering::Relaxed,
            },
            3 => Inst::Cast {
                op: CastOp::PtrToPtr,
                src_ty: Ty::Ptr,
                dst_ty: Ty::Ptr,
                operand: root,
            },
            _ => Inst::Load {
                ty: Ty::I64,
                ptr,
                volatile: true,
                align: None,
            },
        };
        let node = if mode >= 3 {
            InstrNode::new(inst).with_result(ValueId::new(90))
        } else {
            InstrNode::new(inst)
        };
        body.insert(end, node);
        assert_refused(module);
    }
}

#[test]
fn fixed_slots_require_prior_lane_store_and_single_allocation_block() {
    let (mut module, _, _, _) = simple();
    module.functions[0].blocks[0].body.swap(5, 6);
    assert_refused(module);
    let (mut module, _, _, _) = simple();
    let tail = module.functions[0].blocks[0].body.split_off(6);
    module.functions[0].blocks[0]
        .body
        .push(InstrNode::new(Inst::Br {
            target: BlockId::new(1),
            args: vec![],
        }));
    let mut block = Block::new(BlockId::new(1));
    block.body = tail;
    module.functions[0].blocks.push(block);
    assert_refused(module);
    // Backward pointer uses are malformed SSA, not permission to overlook the
    // pre-discovery operands in the complete use census.
    let (mut module, _, _, _) = simple();
    module.functions[0].blocks[0].body.swap(1, 3);
    assert_refused(module);
}

#[test]
fn fixed_slots_require_module_layout_and_preserve_authority_metadata() {
    let (mut module, _, _, _) = simple();
    let function = module.functions[0].clone();
    assert_eq!(promote_allocas_function(&mut module.functions[0]), 0);
    assert_eq!(module.functions[0], function);
    for (triple, pointer_size) in [
        ("i686-unknown-linux-gnu", 4),
        ("avr-unknown-none", 2),
        ("unknown-none", 8),
        ("x86_64-unknown-linux-gnu", 4),
        ("wasm32-unknown-unknown", 4),
    ] {
        let mut candidate = module.clone();
        candidate.target_info = Some(TargetInfo {
            triple: triple.into(),
            pointer_size,
            endianness: Endianness::Little,
            abi: None,
            struct_passing: Default::default(),
        });
        assert_refused(candidate);
    }
    for mode in 0..4 {
        let mut candidate = module.clone();
        match mode {
            0 => candidate.functions[0].proofs.push(ProofAnnotation::NoPanic),
            1 => candidate.functions[0].blocks[0].body[0]
                .proofs
                .push(ProofAnnotation::NoOverflow),
            2 => candidate.proof_obligations.push(ProofObligation::new(
                ProofId::new(0),
                ObligationKind::TranslationValidation,
                ProofStatus::Pending,
                "guard",
            )),
            _ => candidate.functions[0].blocks[0].body[0].proof_context = Some(Default::default()),
        }
        assert_refused(candidate);
    }
    module.functions[0].body_gate = Some(BodyGate::Ungated);
    promote_allocas_module(&mut module);
    assert_eq!(module.functions[0].body_gate, Some(BodyGate::Ungated));
}

#[test]
fn fixed_slots_forward_between_candidates_and_keep_names_closed() {
    for ty in [
        Ty::I8,
        Ty::U8,
        Ty::I16,
        Ty::U16,
        Ty::I32,
        Ty::U32,
        Ty::I64,
        Ty::U64,
        Ty::I128,
        Ty::U128,
    ] {
        let mut f = Fixture::new();
        // Match the real frontend's signed I32 element-count representation.
        let count = f.integer(Ty::I32, 2);
        let a = f.emit(Inst::Alloca {
            ty: ty.clone(),
            count: Some(count),
            align: None,
        });
        let b = f.emit(Inst::Alloca {
            ty: ty.clone(),
            count: Some(count),
            align: None,
        });
        let value = f.integer(ty.clone(), 7);
        f.store(ty.clone(), a, value);
        let first = f.load(ty.clone(), a);
        f.store(ty.clone(), b, first);
        let second = f.load(ty.clone(), b);
        let mut module = f.finish(&[(second, ty.clone())]);
        module.functions[0].value_names = Some(vec![
            (value, "value".into()),
            (first, "first".into()),
            (second, "second".into()),
            (a, "address-a".into()),
        ]);
        module.functions[0].source_provenance = Some(crate::SourceProvenance::new(
            crate::proof::ProofDigest::sha256([1; 32]),
            crate::proof::ProofDigest::sha256([2; 32]),
            vec![],
        ));
        let expected = run(&module);
        let before_len = module.functions[0].blocks[0].body.len();
        promote_allocas_module(&mut module);
        assert_eq!(run(&module), expected);
        assert_eq!(expected, vec![InterpretValue::int(ty, 7).unwrap()]);
        assert_eq!(before_len - module.functions[0].blocks[0].body.len(), 6);
        assert!(module.functions[0].source_provenance.is_none());
        assert_eq!(
            module.functions[0].value_names.as_deref(),
            Some(&[(value, "value".into())][..])
        );
    }
}

#[test]
fn fixed_slots_summary_only_address_and_load_bindings_remain_authoritative() {
    for use_address in [false, true] {
        let (mut module, root, _, loaded) = simple();
        let address = ValueId::new(80);
        let body = &mut module.functions[0].blocks[0].body;
        body.insert(
            body.len() - 1,
            InstrNode::new(Inst::Cast {
                op: CastOp::PtrToInt,
                src_ty: Ty::Ptr,
                dst_ty: Ty::I64,
                operand: root,
            })
            .with_result(address),
        );
        let mut clause = ProofFormula::smtlib2("(= named named)", "Bool");
        clause.bindings.push((
            "named".into(),
            ClauseBinding {
                sort: ClauseSort::BitVec(64),
                place: ClausePlace::Value(if use_address { address } else { loaded }),
            },
        ));
        let mut summary = crate::FunctionSummary::new();
        summary.ensures.push(clause);
        module.functions[0].summary = Some(summary);
        module.functions[0].source_provenance = Some(crate::SourceProvenance::new(
            crate::proof::ProofDigest::sha256([1; 32]),
            crate::proof::ProofDigest::sha256([2; 32]),
            vec![],
        ));
        assert_refused(module);
    }
}

#[test]
fn fixed_slots_unknown_counts_overflowing_offsets_and_duplicate_ids_refuse() {
    let (mut module, _, _, _) = simple();
    // A dynamic, even explicitly typed count is not a known finite allocation.
    module.functions[0].blocks[0].body[0].inst = Inst::Copy {
        ty: Ty::U64,
        operand: ValueId::new(90),
    };
    assert_refused(module);
    for chained in [false, true] {
        let mut f = Fixture::new();
        let root = f.array(Ty::I8, i128::from(u64::MAX));
        let one = f.integer(Ty::U64, 1);
        let max = f.integer(Ty::U64, i128::from(u64::MAX));
        let base = if chained {
            f.gep(Ty::I8, root, &[1])
        } else {
            root
        };
        let indices = if chained { vec![max] } else { vec![max, one] };
        let ptr = f.emit(Inst::GEP {
            pointee_ty: Ty::I8,
            base,
            indices,
            inbounds: true,
        });
        let value = f.integer(Ty::I8, 7);
        f.store(Ty::I8, ptr, value);
        let result = f.load(Ty::I8, ptr);
        assert_refused(f.finish(&[(result, Ty::I8)]));
    }
    let (mut module, _, _, _) = simple();
    // Duplicate IDs are checked even when the second type is deliberately not
    // retained in the integer-only definition-fact map.
    let duplicate = module.functions[0].blocks[0].body[0].results[0];
    let body = &mut module.functions[0].blocks[0].body;
    body.insert(
        body.len() - 1,
        InstrNode::new(Inst::Const {
            ty: Ty::F64,
            value: Constant::Float(0.0),
        })
        .with_result(duplicate),
    );
    assert_refused(module);
}
