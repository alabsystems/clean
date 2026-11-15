// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use trust_ir::interpret::{InterpretErrorCode, InterpretOptions, Interpreter, InterpreterModule};
use trust_ir::value::{BlockId, FuncId, FuncTyId, ValueId};
use trust_ir::{
    Block, Constant, FuncTy, Function, Inst, InstrNode, Module, StorageLayout, StorageSite,
    StorageViolation, StorageViolationKind, Ty,
};

fn returns_integer() -> Module {
    let mut module = Module::new("storage_policy_inventory");
    module
        .func_types
        .push(FuncTy::unrecorded(vec![], vec![Ty::I64], false));
    let mut function = Function::new(FuncId::new(0), "entry", FuncTyId::new(0), BlockId::new(0));
    let mut block = Block::new(BlockId::new(0));
    block.body.push(
        InstrNode::new(Inst::Const {
            ty: Ty::I64,
            value: Constant::Int(7),
        })
        .with_result(ValueId::new(0)),
    );
    block.body.push(InstrNode::new(Inst::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    module
}

#[test]
fn storage_free_module_avoids_reach_solve_and_still_executes() {
    let mut module = returns_integer();
    // A shared nominal chain exercises the ordinary repeated-entry workload.
    let mut ty = Ty::I64;
    for _ in 0..128 {
        let id = module.add_type(ty).unwrap();
        ty = Ty::Array(id, 2);
        module
            .func_types
            .push(FuncTy::unrecorded(vec![ty.clone()], vec![], false));
    }
    let layouts = module.layout_table();
    let mut violations = vec![];
    module.visit_storage_violations(&layouts, |v| violations.push(v));
    assert!(violations.is_empty());
    assert_eq!(layouts.stats().reach_steps, 0);
    let interpreter = Interpreter::with_module(&module);
    for _ in 0..8 {
        let result = interpreter.execute_func(FuncId::new(0), []).unwrap();
        assert_eq!(result.returns.len(), 1);
        assert_eq!(result.returns[0].ty, Ty::I64);
    }
}

#[test]
fn unused_storage_and_pointer_pointees_keep_full_ordered_scan() {
    let mut module = returns_integer();
    let bad = StorageLayout {
        size_bytes: 8,
        align_bytes: 3,
    };
    module.types.push(Ty::PtrConst(Box::new(Ty::Storage(bad))));
    let good = StorageLayout {
        size_bytes: 8,
        align_bytes: 8,
    };
    module
        .func_types
        .push(FuncTy::unrecorded(vec![Ty::Storage(good)], vec![], false));
    let layouts = module.layout_table();
    let mut violations = vec![];
    module.visit_storage_violations(&layouts, |v| violations.push(v));
    assert_eq!(
        violations,
        vec![
            StorageViolation {
                site: StorageSite::TypeOccurrence(1),
                kind: StorageViolationKind::InvalidGeometry(bad)
            },
            StorageViolation {
                site: StorageSite::Signature {
                    signature: 1,
                    result: false,
                    slot: 0
                },
                kind: StorageViolationKind::ValueTraffic
            },
        ]
    );
    assert_eq!(
        module.first_storage_violation(),
        violations.first().copied()
    );
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_func(FuncId::new(0), [])
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
}

#[test]
fn foreign_body_storage_is_not_covered_by_module_absence() {
    let module = returns_integer();
    let mut foreign = module.functions[0].clone();
    foreign.blocks[0].params.push((
        ValueId::new(10),
        Ty::Storage(StorageLayout {
            size_bytes: 8,
            align_bytes: 8,
        }),
    ));
    assert!(module.first_storage_violation().is_none());
    assert_eq!(
        Interpreter::with_module(&module)
            .execute_function(&foreign, [])
            .unwrap_err()
            .code,
        InterpretErrorCode::TypeError
    );
}

#[test]
fn foreign_layout_table_keeps_its_existing_reference_meaning() {
    let mut module = returns_integer();
    let id = module.add_type(Ty::I64).unwrap();
    module
        .func_types
        .push(FuncTy::unrecorded(vec![Ty::Array(id, 1)], vec![], false));
    let mut foreign = Module::new("foreign_layouts");
    foreign
        .add_type(Ty::Storage(StorageLayout::new(8, 8)))
        .unwrap();
    let layouts = foreign.layout_table();
    let mut violations = vec![];
    module.visit_storage_violations(&layouts, |v| violations.push(v));
    assert_eq!(
        violations,
        vec![StorageViolation {
            site: StorageSite::Signature {
                signature: 1,
                result: false,
                slot: 0
            },
            kind: StorageViolationKind::ValueTraffic,
        }]
    );
}

#[test]
fn valid_unused_storage_geometry_remains_allowed() {
    let mut module = returns_integer();
    module
        .types
        .push(Ty::PtrConst(Box::new(Ty::Storage(StorageLayout::new(
            8, 8,
        )))));
    assert_eq!(module.first_storage_violation(), None);
    Interpreter::with_module(&module)
        .execute_func(FuncId::new(0), [])
        .unwrap();
}

#[test]
fn shared_module_preflight_keeps_execution_options_and_fuel_local() {
    let module = returns_integer();
    let owner = InterpreterModule::new(&module);
    let interpreter = owner.interpreter();
    let first = interpreter.execute_func(FuncId::new(0), []).unwrap();
    assert_eq!(first.returns[0].as_int().unwrap().as_signed(), 7);
    let error = interpreter
        .with_options(InterpretOptions {
            fuel: 0,
            ..InterpretOptions::default()
        })
        .execute_func(FuncId::new(0), [])
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::OutOfFuel);
    let fresh_run = owner
        .interpreter()
        .execute_func(FuncId::new(0), [])
        .unwrap();
    assert_eq!(fresh_run.returns[0].as_int().unwrap().as_signed(), 7);
}

#[test]
fn new_immutable_borrow_rechecks_changed_module_before_consuming_arguments() {
    let mut module = returns_integer();
    {
        let owner = InterpreterModule::new(&module);
        assert!(owner.interpreter().execute_func(FuncId::new(0), []).is_ok());
    }
    // Same module object and function IDs, but a new borrow after mutation.
    module.types.push(Ty::Storage(StorageLayout {
        size_bytes: 8,
        align_bytes: 3,
    }));
    {
        let owner = InterpreterModule::new(&module);
        for _ in 0..2 {
            let consumed = std::cell::Cell::new(false);
            let arguments = std::iter::from_fn(|| {
                consumed.set(true);
                None
            });
            let error = owner
                .interpreter()
                .execute_func(FuncId::new(0), arguments)
                .unwrap_err();
            assert_eq!(error.code, InterpretErrorCode::TypeError);
            assert!(!consumed.get(), "module refusal precedes execution setup");
        }
    }
    module.types.clear();
    let owner = InterpreterModule::new(&module);
    assert!(owner.interpreter().execute_func(FuncId::new(0), []).is_ok());
}

#[test]
fn cached_module_policy_does_not_authorize_a_foreign_function_body() {
    let module = returns_integer();
    let owner = InterpreterModule::new(&module);
    let interpreter = owner.interpreter();
    assert!(interpreter.execute_func(FuncId::new(0), []).is_ok());
    let mut foreign = module.functions[0].clone();
    foreign.blocks[0]
        .params
        .push((ValueId::new(9), Ty::Storage(StorageLayout::new(8, 8))));
    let consumed = std::cell::Cell::new(false);
    let arguments = std::iter::from_fn(|| {
        consumed.set(true);
        None
    });
    let error = interpreter
        .execute_function(&foreign, arguments)
        .unwrap_err();
    assert_eq!(error.code, InterpretErrorCode::TypeError);
    assert!(!consumed.get(), "foreign bodies retain their own preflight");
}
