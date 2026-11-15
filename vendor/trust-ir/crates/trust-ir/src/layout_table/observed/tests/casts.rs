// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored cast controls. All controls in this successor are UNRUN.

use super::*;

mod controls;
use crate::ty::{EnumVariant, RecordDef};
use crate::{CastLayoutEvidence, CastOp, FatPtrKind, FuncTy, HandleTy, RecordId};

fn run(
    module: &Module,
    op: CastOp,
    src: &Ty,
    dst: &Ty,
    observer: &mut Observer,
) -> Result<Result<CastLayoutEvidence, LayoutError>, ObservedValueError> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    let table = LayoutTable::new_observed(module, &mut session, site())?;
    assert!(core::ptr::eq(table.module, module));
    table.layout_sensitive_cast_evidence_observed(op, src, dst, &mut session, site())
}

fn equal(module: &Module, op: CastOp, src: &Ty, dst: &Ty) {
    let expected = LayoutTable::new(module).layout_sensitive_cast_evidence(op, src, dst);
    let actual = run(module, op, src, dst, &mut Observer::default()).unwrap();
    assert_eq!(actual, expected, "{op:?}: {src:?} -> {dst:?}");
}

#[test]
fn scalar_pointer_and_reification_evidence_and_error_order_match() {
    let module = fixture();
    for (op, src, dst) in [
        (
            CastOp::Trunc,
            Ty::Handle(Box::new(HandleTy::new("n", "r"))),
            Ty::Bool,
        ),
        (CastOp::Bitcast, Ty::U64, Ty::I64),
        (CastOp::Transmute, Ty::U8, Ty::U64),
        (CastOp::Bitcast, Ty::Bool, Ty::Bool),
        (CastOp::Bitcast, Ty::Bool, Ty::U8),
        (CastOp::Bitcast, Ty::Vector(Box::new(Ty::Bool), 8), Ty::U64),
        (CastOp::PtrToPtr, Ty::Ptr, Ty::Ref(Box::new(Ty::Bool))),
        (CastOp::PtrToPtr, Ty::U64, Ty::U64),
        (CastOp::PtrToPtr, Ty::Ptr, Ty::FatPtr(FatPtrKind::Str)),
        (
            CastOp::PtrToPtr,
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::ContainerVtable),
        ),
        (
            CastOp::PtrToPtr,
            Ty::FatPtr(FatPtrKind::Str),
            Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        ),
        (
            CastOp::ReifyFnPointer,
            Ty::Func(FuncTyId::new(404)),
            Ty::Ptr,
        ),
        (CastOp::ReifyFnPointer, Ty::U64, Ty::Ptr),
        (
            CastOp::ReifyFnPointer,
            Ty::Func(FuncTyId::new(404)),
            Ty::FatPtr(FatPtrKind::Str),
        ),
        (
            CastOp::ReifyFnPointer,
            Ty::Func(FuncTyId::new(404)),
            Ty::U64,
        ),
    ] {
        equal(&module, op, &src, &dst);
    }
}

#[test]
fn handles_follow_all_original_named_axes_and_inline_pointer_children() {
    let mut module = Module::new("cast_handle_axes");
    module
        .types
        .push(Ty::Handle(Box::new(HandleTy::new("h", "runtime"))));
    module.func_types.push(FuncTy::unrecorded(
        vec![Ty::Array(TyId::new(0), 0)],
        vec![],
        false,
    ));
    module.func_types.push(FuncTy::unrecorded(
        vec![],
        vec![Ty::Refine(TyId::new(0), crate::PredId::new(0))],
        false,
    ));
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![],
    });
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(404),
        captures: vec![Ty::Array(TyId::new(0), 1)],
    });
    module.structs.push(structure(
        8,
        vec![field("h", Ty::Sequence(TyId::new(0)), None)],
        8,
        8,
    ));
    module.enums.push(EnumDef::new(
        EnumId::new(9),
        "e",
        vec![EnumVariant {
            name: "v".into(),
            fields: vec![Ty::Set(TyId::new(0), crate::ty::SetRepr::Boxed)],
            field_names: vec![],
        }],
    ));
    module.records.push(RecordDef {
        id: RecordId::new(10),
        name: "r".into(),
        fields: vec![field("f", Ty::Func(FuncTyId::new(0)), None)],
    });
    for src in [
        Ty::Array(TyId::new(0), 0),
        Ty::Refine(TyId::new(0), crate::PredId::new(0)),
        Ty::Sequence(TyId::new(0)),
        Ty::Set(TyId::new(0), crate::ty::SetRepr::Boxed),
        Ty::FatPtr(FatPtrKind::Slice(TyId::new(0))),
        Ty::Func(FuncTyId::new(0)),
        Ty::Func(FuncTyId::new(1)),
        Ty::Closure(ClosureTyId::new(0)),
        Ty::Closure(ClosureTyId::new(1)),
        Ty::Struct(StructId::new(8)),
        Ty::Enum(EnumId::new(9)),
        Ty::Record(RecordId::new(10)),
        Ty::Ref(Box::new(Ty::Tuple(vec![Ty::Array(TyId::new(0), 1)]))),
    ] {
        equal(&module, CastOp::ReifyFnPointer, &src, &Ty::Ptr);
        assert!(matches!(
            run(
                &module,
                CastOp::ReifyFnPointer,
                &src,
                &Ty::Ptr,
                &mut Observer::default()
            )
            .unwrap(),
            Err(LayoutError::OpaqueHandleCast { .. })
        ));
    }
}

#[test]
fn cycles_missing_references_and_later_duplicate_seed_preserve_reachability() {
    let mut module = Module::new("cast_cycle");
    module.structs.push(structure(
        1,
        vec![field("cycle", Ty::Struct(StructId::new(1)), None)],
        0,
        1,
    ));
    let src = Ty::Ref(Box::new(Ty::Struct(StructId::new(1))));
    equal(&module, CastOp::PtrToPtr, &src, &Ty::Ptr);
    assert!(
        run(
            &module,
            CastOp::PtrToPtr,
            &src,
            &Ty::Ptr,
            &mut Observer::default()
        )
        .unwrap()
        .is_ok()
    );
    module.structs.push(structure(
        1,
        vec![field(
            "late",
            Ty::Handle(Box::new(HandleTy::new("h", "r"))),
            None,
        )],
        8,
        8,
    ));
    equal(&module, CastOp::PtrToPtr, &src, &Ty::Ptr);
    assert!(matches!(
        run(
            &module,
            CastOp::PtrToPtr,
            &src,
            &Ty::Ptr,
            &mut Observer::default()
        )
        .unwrap(),
        Err(LayoutError::OpaqueHandleCast { .. })
    ));
    for src in [
        Ty::Ref(Box::new(Ty::Array(TyId::new(404), 1))),
        Ty::Func(FuncTyId::new(404)),
    ] {
        equal(&module, CastOp::PtrToPtr, &src, &Ty::Ptr);
    }
}

#[test]
fn by_value_closure_and_bool_boundaries_match_including_records() {
    let mut module = fixture();
    module.records.push(RecordDef {
        id: RecordId::new(10),
        name: "bool_record".into(),
        fields: vec![field("b", Ty::Bool, None)],
    });
    module.records.push(RecordDef {
        id: RecordId::new(11),
        name: "closure_record".into(),
        fields: vec![field("c", Ty::Closure(ClosureTyId::new(0)), None)],
    });
    for src in [
        Ty::Closure(ClosureTyId::new(404)),
        Ty::Tuple(vec![Ty::Closure(ClosureTyId::new(0))]),
        Ty::Record(RecordId::new(11)),
    ] {
        equal(&module, CastOp::Bitcast, &src, &Ty::U64);
        assert!(matches!(
            run(
                &module,
                CastOp::Bitcast,
                &src,
                &Ty::U64,
                &mut Observer::default()
            )
            .unwrap(),
            Err(LayoutError::ClosureCast { .. })
        ));
    }
    let record = Ty::Record(RecordId::new(10));
    equal(&module, CastOp::Bitcast, &record, &Ty::U64);
    assert!(!matches!(
        run(
            &module,
            CastOp::Bitcast,
            &record,
            &Ty::U64,
            &mut Observer::default()
        )
        .unwrap(),
        Err(LayoutError::BoolLaneReinterpret { .. })
    ));
    for child in [Ty::Closure(ClosureTyId::new(0)), Ty::Bool] {
        equal(
            &module,
            CastOp::PtrToPtr,
            &Ty::Ref(Box::new(child)),
            &Ty::Ptr,
        );
    }
    module.func_types.push(FuncTy::unrecorded(
        vec![Ty::Closure(ClosureTyId::new(0)), Ty::Bool],
        vec![],
        false,
    ));
    equal(
        &module,
        CastOp::PtrToPtr,
        &Ty::Func(FuncTyId::new(0)),
        &Ty::Ptr,
    );
}

#[test]
fn handle_guard_precedes_closure_and_layout_tampering_changes_evidence() {
    let mut module = fixture();
    let closure = Ty::Closure(ClosureTyId::new(0));
    let handle = Ty::Handle(Box::new(HandleTy::new("h", "r")));
    equal(&module, CastOp::Bitcast, &closure, &handle);
    assert!(matches!(
        run(
            &module,
            CastOp::Bitcast,
            &closure,
            &handle,
            &mut Observer::default()
        )
        .unwrap(),
        Err(LayoutError::OpaqueHandleCast { .. })
    ));
    let src = Ty::Struct(StructId::new(91));
    equal(&module, CastOp::Transmute, &src, &Ty::U64);
    module.structs[0].size = Some(12);
    equal(&module, CastOp::Transmute, &src, &Ty::U64);
    assert!(matches!(
        run(
            &module,
            CastOp::Transmute,
            &src,
            &Ty::U64,
            &mut Observer::default()
        )
        .unwrap(),
        Err(LayoutError::CastSizeMismatch { .. })
    ));
}

#[test]
fn bool_and_closure_seeds_follow_array_refinement_struct_and_enum_tables() {
    let mut module = Module::new("cast_value_axes");
    module.types.push(Ty::Bool);
    module.types.push(Ty::Closure(ClosureTyId::new(404)));
    for (id, entry) in [(2, 0), (3, 1)] {
        module.structs.push(structure(
            id,
            vec![field("member", Ty::Array(TyId::new(entry), 0), None)],
            0,
            1,
        ));
        module.enums.push(EnumDef::new(
            EnumId::new(id),
            "value_seed",
            vec![EnumVariant {
                name: "v".into(),
                fields: vec![Ty::Refine(TyId::new(entry), crate::PredId::new(0))],
                field_names: vec![],
            }],
        ));
    }
    for (entry, id) in [(0, 2), (1, 3)] {
        for src in [
            Ty::Array(TyId::new(entry), 0),
            Ty::Refine(TyId::new(entry), crate::PredId::new(0)),
            Ty::Struct(StructId::new(id)),
            Ty::Enum(EnumId::new(id)),
        ] {
            equal(&module, CastOp::Transmute, &src, &Ty::U64);
            let result = run(
                &module,
                CastOp::Transmute,
                &src,
                &Ty::U64,
                &mut Observer::default(),
            )
            .unwrap();
            assert!(if entry == 0 {
                matches!(result, Err(LayoutError::BoolLaneReinterpret { .. }))
            } else {
                matches!(result, Err(LayoutError::ClosureCast { .. }))
            });
        }
    }
}
