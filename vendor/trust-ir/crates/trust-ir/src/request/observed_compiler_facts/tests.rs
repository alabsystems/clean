// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::interpret::InterpretOptions;
use crate::request::{
    NativeCompilerFactId, NativeEnumNicheFact, NativeEnumVariantLayoutFact, NativeIntegerRange,
};
use crate::ty::FatPtrKind;
use crate::{
    Endianness, EnumId, EnumVariant, FieldDef, FuncId, PointerLayoutShape, PointerMetadataShape,
    StructDef, StructId, StructRepr, TargetInfo, TyId, TyShape,
};

mod parity;
mod primitives;
mod stops;

#[derive(Default)]
struct Observer {
    events: Vec<ExecutionProgress>,
    stop_at: Option<usize>,
    stop_retirement: bool,
    work: usize,
    bytes: usize,
    work_limit: Option<usize>,
    byte_limit: Option<usize>,
}
impl ExecutionObserver for Observer {
    type Refusal = &'static str;
    fn admit(&mut self, event: ExecutionProgress) -> Result<(), Self::Refusal> {
        self.events.push(event);
        if self.stop_at == Some(self.events.len()) {
            return Err("interior");
        }
        if self.stop_retirement && event.phase == ExecutionPhase::ScratchRetirement {
            return Err("retirement");
        }
        self.work = self.work.checked_add(event.work).ok_or("work overflow")?;
        self.bytes = self
            .bytes
            .checked_add(event.copy_bytes)
            .ok_or("copy overflow")?;
        if self.work_limit.is_some_and(|cap| self.work > cap) {
            return Err("work");
        }
        if self.byte_limit.is_some_and(|cap| self.bytes > cap) {
            return Err("bytes");
        }
        Ok(())
    }
}
fn site() -> ExecutionSite {
    ExecutionSite::Entry(FuncId::new(973))
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
fn module() -> Module {
    let mut module = Module::new("compiler-fact-constituents");
    module.target_info = Some(target());
    module.structs.push(StructDef {
        id: StructId::new(9),
        name: "s".into(),
        fields: vec![
            FieldDef {
                name: "λ".repeat(1100),
                ty: Ty::U64,
                offset: Some(0),
            },
            FieldDef {
                name: "b".into(),
                ty: Ty::U32,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::Rust,
        origin: None,
    });
    module.enums.push(EnumDef::new(
        EnumId::new(7),
        "e",
        vec![
            EnumVariant {
                name: "κ🦀".repeat(400),
                fields: vec![Ty::U32],
                field_names: vec![],
            },
            EnumVariant {
                name: "second".into(),
                fields: vec![],
                field_names: vec![],
            },
        ],
    ));
    module
}
fn structure(module: &Module) -> NativeAdtLayoutFact {
    NativeAdtLayoutFact {
        id: NativeCompilerFactId::new(1),
        ty: Ty::Struct(StructId::new(9)),
        layout: (*LayoutTable::new(module)
            .ty_layout(&Ty::Struct(StructId::new(9)))
            .unwrap())
        .clone(),
        enum_layout: None,
    }
}
fn enumeration(module: &Module) -> NativeAdtLayoutFact {
    NativeAdtLayoutFact {
        id: NativeCompilerFactId::new(2),
        ty: Ty::Enum(EnumId::new(7)),
        layout: TyLayoutShape {
            size_bits: 64,
            align_bits: Some(32),
            kind: TyLayoutKind::Enum {
                id: EnumId::new(7),
                variants: 2,
            },
        },
        enum_layout: Some(NativeEnumLayoutFact {
            enum_id: EnumId::new(7),
            tag_encoding: NativeEnumTagEncoding::Direct,
            tag_bits: Some(8),
            discriminant_offset_bits: Some(0),
            niche: None,
            variants: vec![
                NativeEnumVariantLayoutFact {
                    variant_index: 0,
                    name: module.enums[0].variants[0].name.clone(),
                    discriminant: Some(0),
                    fields: vec![FieldOffsetShape {
                        field: 0,
                        name: "ignored".into(),
                        ty_shape: TyShape::Int {
                            signed: false,
                            bits: 32,
                        },
                        offset_bits: Some(32),
                    }],
                    size_bits: 32,
                    align_bits: Some(32),
                },
                NativeEnumVariantLayoutFact {
                    variant_index: 1,
                    name: "second".into(),
                    discriminant: Some(1),
                    fields: vec![],
                    size_bits: 0,
                    align_bits: Some(8),
                },
            ],
        }),
    }
}
fn fat() -> NativeFatPointerFact {
    NativeFatPointerFact {
        id: NativeCompilerFactId::new(3),
        ty: Ty::FatPtr(FatPtrKind::Str),
        layout: PointerLayoutShape::fat(64, PointerMetadataShape::StrLen),
    }
}
fn ordinary_adt(module: &Module, fact: &NativeAdtLayoutFact) -> Vec<E> {
    let mut errors = Vec::new();
    crate::request::validate_adt_layout_fact(&LayoutTable::new(module), fact, &mut errors);
    errors
}
fn ordinary_enum(module: &Module, fact: &NativeAdtLayoutFact) -> Vec<E> {
    let mut errors = Vec::new();
    crate::request::validate_native_enum_layout_fact(
        fact,
        fact.enum_layout.as_ref().unwrap(),
        &module.enums[0],
        &mut errors,
    );
    errors
}
fn ordinary_fat(module: &Module, fact: &NativeFatPointerFact) -> Vec<E> {
    let mut errors = Vec::new();
    crate::request::validate_fat_pointer_fact(module, fact, &mut errors);
    errors
}
fn adt(module: &Module, fact: &NativeAdtLayoutFact) -> Vec<E> {
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    let table = LayoutTable::new_observed(module, &mut session, site()).unwrap();
    let errors = fact
        .validation_errors_observed(&table, &mut session, site())
        .unwrap();
    assert!(session.first_refusal().is_none());
    assert_eq!(session.remaining_fuel(), InterpretOptions::default().fuel);
    assert!(observer.events.iter().all(|event| event.site == site()));
    errors
}

#[derive(Clone, Copy)]
enum Case {
    Struct,
    Enum,
    EnumHelper,
    Fat,
}
fn run(
    module: &Module,
    structure: &NativeAdtLayoutFact,
    enumeration: &NativeAdtLayoutFact,
    fat: &NativeFatPointerFact,
    case: Case,
    session: &mut ObservedSession<'_, Observer>,
) -> R<Vec<E>> {
    match case {
        Case::Struct | Case::Enum => {
            let table = LayoutTable::new_observed(module, session, site())?;
            let fact = if matches!(case, Case::Struct) {
                structure
            } else {
                enumeration
            };
            fact.validation_errors_observed(&table, session, site())
        }
        Case::EnumHelper => enumeration
            .enum_layout
            .as_ref()
            .unwrap()
            .validation_errors_observed(enumeration, &module.enums[0], session, site()),
        Case::Fat => fat.validation_errors_observed(module, session, site()),
    }
}
