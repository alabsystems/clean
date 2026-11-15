// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

//! Source-authored controls; execution is deliberately UNRUN in this task.

use super::*;
use crate::interpret::InterpretOptions;
use crate::ty::ClosureTy;
use crate::{Endianness, FuncId, FuncTyId, TargetInfo};

mod casts;
mod enums;
mod lazy_memo;
mod owning_retirement;
mod scratch_retirement;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}

impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, progress: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(progress);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        self.work = self
            .work
            .checked_add(progress.work)
            .ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(progress.copy_bytes)
            .ok_or("byte overflow")?;
        if self.work_limit.is_some_and(|limit| self.work > limit) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|limit| self.bytes > limit) {
            return Err("bytes");
        }
        Ok(())
    }
}

fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(79))
}
fn target() -> TargetInfo {
    TargetInfo {
        triple: "x86_64-unknown-linux-gnu".into(),
        pointer_size: 8,
        endianness: Endianness::Little,
        abi: None,
        struct_passing: Default::default(),
    }
}
fn structure(id: u32, fields: Vec<FieldDef>, size: u64, align: u64) -> StructDef {
    StructDef {
        id: StructId::new(id),
        name: format!("s{id}"),
        fields,
        size: Some(size),
        align: Some(align),
        repr: StructRepr::Rust,
        origin: None,
    }
}
fn field(name: &str, ty: Ty, offset: Option<u64>) -> FieldDef {
    FieldDef {
        name: name.into(),
        ty,
        offset,
    }
}
fn fixture() -> Module {
    let mut module = Module::new("observed_layout");
    module.target_info = Some(target());
    module.types.push(Ty::U32);
    module
        .types
        .push(Ty::Tuple(vec![Ty::U8, Ty::U64, Ty::Unit]));
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(1),
        size: 16,
        align: 8,
        field_offsets: vec![8, 0, 16],
    });
    module.closure_types.push(ClosureTy {
        func: FuncTyId::new(0),
        captures: vec![Ty::U8, Ty::U64],
    });
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(0),
        size: 16,
        align: 8,
        capture_offsets: vec![8, 0],
    });
    module.structs.push(structure(
        91,
        vec![
            field("a", Ty::U32, Some(0)),
            field("β".repeat(1100).as_str(), Ty::U32, Some(4)),
            field("zst", Ty::Unit, None),
        ],
        8,
        4,
    ));
    module
}
fn observed(
    module: &Module,
    ty: &Ty,
    observer: &mut Observer,
) -> Result<Result<Arc<TyLayoutShape>, LayoutError>, ObservedValueError> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    let table = LayoutTable::new_observed(module, &mut session, site())?;
    assert!(core::ptr::eq(table.module, module));
    table.ty_layout_observed(ty, &mut session, site())
}
fn parity(module: &Module, ty: &Ty) {
    let expected = LayoutTable::new(module).ty_layout(ty);
    let actual = observed(module, ty, &mut Observer::default()).unwrap();
    match (actual, expected) {
        (Ok(actual), Ok(expected)) => assert_eq!(*actual, *expected),
        (Err(actual), Err(expected)) => assert_eq!(actual, expected),
        (actual, expected) => panic!("layout differs: {actual:?} / {expected:?}"),
    }
}

#[test]
fn scalar_vector_array_refinement_and_reordered_aggregate_layouts_match() {
    let module = fixture();
    for ty in [
        Ty::I128,
        Ty::Bool,
        Ty::Char,
        Ty::Usize,
        Ty::Ptr,
        Ty::Unit,
        Ty::Never,
        Ty::Vector(Box::new(Ty::U32), 17),
        Ty::Array(TyId::new(0), 19),
        Ty::Refine(TyId::new(0), crate::PredId::new(3)),
        Ty::Struct(StructId::new(91)),
        module.types[1].clone(),
        Ty::Closure(ClosureTyId::new(0)),
    ] {
        parity(&module, &ty);
    }
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
    assert_eq!(
        table
            .validate_tuple_layouts_observed(&mut session, site())
            .unwrap(),
        table.validate_tuple_layouts()
    );
    assert_eq!(
        table
            .validate_closure_layouts_observed(&mut session, site())
            .unwrap(),
        table.validate_closure_layouts()
    );
    assert!(
        observer
            .events
            .iter()
            .all(|progress| progress.site == site())
    );
}

#[test]
fn tampered_offsets_overlap_alignment_transparent_and_missing_fields_match() {
    let base = fixture();
    for change in 0..9 {
        let mut module = base.clone();
        match change {
            0 => module.structs[0].fields[1].offset = Some(0),
            1 => module.structs[0].fields[0].offset = None,
            2 => module.structs[0].align = Some(3),
            3 => module.structs[0].size = Some(4),
            4 => module.structs[0].repr = StructRepr::Transparent,
            5 => module.structs[0].repr = StructRepr::Packed(0),
            6 => module.tuple_layouts[0].field_offsets[0] = 0,
            7 => module.closure_layouts[0].capture_offsets[0] = 1,
            _ => module.tuple_layouts[0]
                .field_offsets
                .pop()
                .map(|_| ())
                .unwrap(),
        }
        parity(&module, &Ty::Struct(StructId::new(91)));
        parity(&module, &module.types[1]);
        parity(&module, &Ty::Closure(ClosureTyId::new(0)));
    }
    let mut module = base;
    module.structs[0] = structure(91, vec![field("packed", Ty::U32, Some(1))], 5, 1)
        .with_repr(StructRepr::Packed(1));
    parity(&module, &Ty::Struct(StructId::new(91)));
    module.structs[0] = structure(
        91,
        vec![
            field("carrier", Ty::U32, Some(0)),
            field("unit", Ty::Unit, None),
        ],
        4,
        4,
    )
    .with_repr(StructRepr::Transparent);
    parity(&module, &Ty::Struct(StructId::new(91)));
}

#[test]
fn original_cycle_first_definition_and_descriptor_refusal_order_are_preserved() {
    let mut module = fixture();
    module.structs.push(structure(
        91,
        vec![field("duplicate", Ty::Never, Some(0))],
        0,
        1,
    ));
    parity(&module, &Ty::Struct(StructId::new(91)));
    module.structs[0].fields[0].ty = Ty::Struct(StructId::new(91));
    parity(&module, &Ty::Struct(StructId::new(91)));
    module.types[0] = Ty::Array(TyId::new(0), 1);
    parity(&module, &Ty::Array(TyId::new(0), 2));
    let mut module = fixture();
    module.tuple_layouts.push(module.tuple_layouts[0].clone());
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(99),
        size: 0,
        align: 1,
        field_offsets: vec![],
    });
    parity(&module, &module.types[1]);
    module.tuple_layouts.swap(1, 2);
    parity(&module, &module.types[1]);
    module
        .closure_layouts
        .push(module.closure_layouts[0].clone());
    module.closure_layouts.push(ClosureLayoutDescriptor {
        origin: None,
        closure: ClosureTyId::new(99),
        size: 0,
        align: 1,
        capture_offsets: vec![],
    });
    parity(&module, &Ty::Closure(ClosureTyId::new(0)));
    module.closure_layouts.swap(1, 2);
    parity(&module, &Ty::Closure(ClosureTyId::new(0)));
}

#[test]
fn structural_tuple_identity_keeps_char_u32_and_nested_pointer_payloads_distinct() {
    let mut module = fixture();
    module.types.push(Ty::Tuple(vec![Ty::Char]));
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(2),
        size: 4,
        align: 4,
        field_offsets: vec![0],
    });
    parity(&module, &Ty::Tuple(vec![Ty::Char]));
    parity(&module, &Ty::Tuple(vec![Ty::U32]));
    let ty = Ty::Tuple(vec![Ty::PtrConst(Box::new(Ty::Tuple(vec![
        Ty::Char,
        Ty::U32,
    ])))]);
    module.types.push(ty.clone());
    module.tuple_layouts.push(TupleLayoutDescriptor {
        tuple_type: TyId::new(3),
        size: 8,
        align: 8,
        field_offsets: vec![0],
    });
    parity(&module, &ty);
    parity(
        &module,
        &Ty::Tuple(vec![Ty::PtrConst(Box::new(Ty::Tuple(vec![
            Ty::U32,
            Ty::Char,
        ])))]),
    );
}

#[test]
fn unavailable_targets_and_missing_rows_stay_semantic_errors() {
    let mut module = fixture();
    module.target_info.as_mut().unwrap().triple = format!("i686-{}", "λ".repeat(1400));
    parity(&module, &Ty::U32);
    parity(&module, &Ty::Unit);
    module.target_info = None;
    parity(&module, &module.types[1]);
    parity(&module, &Ty::Closure(ClosureTyId::new(0)));
    parity(&module, &Ty::Struct(StructId::new(99)));
    parity(&module, &Ty::Array(TyId::new(99), 1));
    parity(&module, &Ty::Enum(EnumId::new(99)));
}

#[test]
fn empty_enum_retains_original_semantic_refusal_without_poisoning_the_session() {
    let mut module = fixture();
    module
        .enums
        .push(EnumDef::new(EnumId::new(7), "open_enum", vec![]));
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
    assert_eq!(
        table
            .ty_layout_observed(&Ty::Enum(EnumId::new(7)), &mut session, site())
            .unwrap()
            .unwrap_err(),
        LayoutError::EnumLayoutUnavailable(EnumId::new(7))
    );
    assert!(session.first_refusal().is_none());
    // A semantic refusal does not reset or poison the original grant.
    assert_eq!(
        table
            .ty_layout_observed(&Ty::U32, &mut session, site())
            .unwrap()
            .unwrap()
            .size_bits,
        32
    );
    drop(table);
    module.types[1] = Ty::Tuple(vec![Ty::Enum(EnumId::new(7))]);
    // The original fixture still has three offsets. Preserve the ordinary
    // descriptor-arity refusal before any child layout is queried.
    let expected = LayoutTable::new(&module).validate_tuple_layouts();
    assert_eq!(
        expected,
        Err(LayoutError::TupleLayoutIncoherent(TyId::new(1)))
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
    assert_eq!(
        table
            .validate_tuple_layouts_observed(&mut session, site())
            .unwrap(),
        expected
    );
    assert!(session.first_refusal().is_none());
    drop(table);

    // A coherent one-field descriptor reaches the intended empty-enum child
    // refusal. This is a separate input, not a reset of a refused operation.
    module.tuple_layouts[0].field_offsets = vec![0];
    let expected = LayoutTable::new(&module).validate_tuple_layouts();
    assert_eq!(
        expected,
        Err(LayoutError::EnumLayoutUnavailable(EnumId::new(7)))
    );
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let table = LayoutTable::new_observed(&module, &mut session, site()).unwrap();
    assert_eq!(
        table
            .validate_tuple_layouts_observed(&mut session, site())
            .unwrap(),
        expected
    );
    assert!(session.first_refusal().is_none());
}

#[test]
fn deep_shared_nominal_and_table_reference_paths_match_without_recursive_walks() {
    let mut module = Module::new("deep_observed_layout");
    for id in 0..129 {
        let child = if id == 128 {
            Ty::Unit
        } else {
            Ty::Struct(StructId::new(id + 1))
        };
        module.structs.push(structure(
            id,
            vec![
                field("left", child.clone(), None),
                field("right", child, None),
            ],
            0,
            1,
        ));
        module.types.push(if id == 128 {
            Ty::U8
        } else {
            Ty::Array(TyId::new(id + 1), 1)
        });
    }
    parity(&module, &Ty::Struct(StructId::new(0)));
    parity(&module, &Ty::Array(TyId::new(0), 1));
}
