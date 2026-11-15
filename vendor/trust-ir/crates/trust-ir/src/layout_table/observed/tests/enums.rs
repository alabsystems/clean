// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0 OR MIT

use super::*;
use crate::RecordId;
use crate::ty::{EnumLayoutDescriptor, RecordDef};

mod stops;

fn variant(fields: Vec<Ty>) -> EnumVariant {
    EnumVariant {
        name: "v".into(),
        fields,
        field_names: vec![],
    }
}
fn definition(fields: Vec<Vec<Ty>>) -> EnumDef {
    EnumDef::new(
        EnumId::new(7),
        "enum_layout",
        fields.into_iter().map(variant).collect(),
    )
}
fn enum_module(def: EnumDef) -> Module {
    let mut module = Module::new("observed_enum");
    module.target_info = Some(target());
    module.enums.push(def);
    module
}
fn direct() -> Module {
    let mut def = definition(vec![vec![Ty::U8, Ty::U64], vec![Ty::U16], vec![]]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Direct { tag_offset: 9 },
        size: 16,
        align: 8,
        variant_field_offsets: vec![vec![8, 0], vec![0], vec![]],
    });
    enum_module(def)
}
fn niche() -> Module {
    let mut def = definition(vec![vec![Ty::Char], vec![Ty::Never], vec![Ty::Unit]]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 2,
            niche_variants_end: 2,
            niche_start: 0x11_0000,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U32,
        },
        size: 4,
        align: 4,
        variant_field_offsets: vec![vec![0], vec![0], vec![0]],
    });
    enum_module(def)
}
fn niche_graph() -> Module {
    let mut module = niche();
    module.enums[0].variants[1].fields[0] = Ty::Enum(EnumId::new(8));
    for id in [8, 9] {
        let mut def = EnumDef::new(
            EnumId::new(id),
            "nested_bottom",
            vec![variant(vec![if id == 8 {
                Ty::Enum(EnumId::new(9))
            } else {
                Ty::Never
            }])],
        );
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: 0,
            align: 1,
            variant_field_offsets: vec![vec![0]],
        });
        module.enums.push(def);
    }
    module
}
fn run(
    module: &Module,
    observer: &mut Observer,
) -> Result<Result<Arc<EnumLayoutShape>, LayoutError>, ObservedValueError> {
    let mut session = ObservedSession::new(InterpretOptions::default(), observer);
    let table = LayoutTable::new_observed(module, &mut session, site())?;
    table.enum_layout_observed(EnumId::new(7), &mut session, site())
}
fn equal(module: &Module) {
    let expected = LayoutTable::new(module).enum_layout(EnumId::new(7));
    let actual = run(module, &mut Observer::default()).unwrap();
    match (actual, expected) {
        (Ok(actual), Ok(expected)) => assert_eq!(*actual, *expected),
        (Err(actual), Err(expected)) => assert_eq!(actual, expected),
        (actual, expected) => panic!("enum layout differs: {actual:?} / {expected:?}"),
    }
    parity(module, &Ty::Enum(EnumId::new(7)));
}

#[test]
fn canonical_discriminants_explicit_widths_and_inference_limits_match() {
    let base = definition(vec![vec![], vec![], vec![]]);
    for (discs, repr) in [
        (vec![], None),
        (vec![Some(-2)], None),
        (vec![None, Some(256)], None),
        (vec![Some(1), Some(1)], None),
        (vec![Some(i128::MAX)], Some(EnumTagRepr::I128)),
        (vec![Some(i128::MAX), Some(0)], Some(EnumTagRepr::I128)),
        (vec![Some(u64::MAX as i128), Some(0), Some(1)], None),
        (vec![Some((u64::MAX as i128) + 1), Some(0), Some(1)], None),
        (
            vec![Some(i128::MAX), Some(0), Some(1)],
            Some(EnumTagRepr::U128),
        ),
        (vec![Some(-1)], Some(EnumTagRepr::U128)),
        (vec![Some(0), Some(256)], Some(EnumTagRepr::U8)),
    ] {
        let mut def = base.clone();
        def.discriminants = discs;
        def.repr = repr;
        equal(&enum_module(def));
    }
    equal(&enum_module(definition(vec![])));
    equal(&enum_module(definition(vec![vec![Ty::Never]])));
}

#[test]
fn direct_untagged_reordered_fields_and_descriptor_tampering_match() {
    let base = direct();
    equal(&base);
    for change in 0..8 {
        let mut module = base.clone();
        let desc = module.enums[0].layout.as_mut().unwrap();
        match change {
            0 => desc.variant_field_offsets[0][0] = 0,
            1 => desc.variant_field_offsets[0][1] = 1,
            2 => desc.size = 8,
            3 => desc.align = 3,
            4 => desc.encoding = EnumTagEncoding::Direct { tag_offset: 0 },
            5 => {
                desc.encoding = EnumTagEncoding::Direct {
                    tag_offset: u64::MAX,
                }
            }
            6 => {
                desc.variant_field_offsets.pop();
            }
            _ => desc.variant_field_offsets[0].push(0),
        }
        equal(&module);
    }
    for ty in [Ty::U64, Ty::Unit, Ty::Never] {
        let mut def = definition(vec![vec![ty.clone()]]);
        def.layout = Some(EnumLayoutDescriptor {
            encoding: EnumTagEncoding::Untagged,
            size: if matches!(ty, Ty::U64) { 8 } else { 0 },
            align: if matches!(ty, Ty::U64) { 8 } else { 1 },
            variant_field_offsets: vec![vec![0]],
        });
        equal(&enum_module(def));
    }
}

#[test]
fn niche_unencoded_never_coverage_mask_and_payload_overlap_match() {
    let base = niche();
    equal(&base);
    for change in 0..8 {
        let mut module = base.clone();
        match change {
            0 => module.enums[0].variants[1].fields[0] = Ty::Unit,
            1 => module.enums[0].variants[2].fields[0] = Ty::Char,
            2 => module.enums[0].variants[0].fields[0] = Ty::Unit,
            change => {
                let EnumTagEncoding::Niche {
                    untagged_variant,
                    niche_variants_start,
                    niche_variants_end,
                    niche_start,
                    niche_offset,
                    ..
                } = &mut module.enums[0].layout.as_mut().unwrap().encoding
                else {
                    unreachable!()
                };
                match change {
                    3 => *untagged_variant = 99,
                    4 => *niche_variants_start = 3,
                    5 => *niche_variants_end = 99,
                    6 => *niche_start = u128::MAX,
                    _ => *niche_offset = u64::MAX,
                }
            }
        }
        equal(&module);
    }
    let mut wide = definition(vec![vec![Ty::U128], vec![Ty::Unit]]);
    wide.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Niche {
            untagged_variant: 0,
            niche_variants_start: 1,
            niche_variants_end: 1,
            niche_start: u128::MAX,
            niche_offset: 0,
            niche_ty: EnumTagRepr::U128,
        },
        size: 16,
        align: 16,
        variant_field_offsets: vec![vec![0], vec![0]],
    });
    equal(&enum_module(wide));
}

#[test]
fn niche_inhabitedness_reads_later_duplicate_definitions_and_cycle_equations() {
    let mut module = niche_graph();
    equal(&module);
    assert!(run(&module, &mut Observer::default()).unwrap().is_ok());
    module.enums.push(EnumDef::new(
        EnumId::new(9),
        "later_cycle",
        vec![variant(vec![Ty::Enum(EnumId::new(9))])],
    ));
    equal(&module);
    assert_eq!(
        run(&module, &mut Observer::default()).unwrap().unwrap_err(),
        LayoutError::EnumLayoutUnavailable(EnumId::new(7))
    );
}

#[test]
fn enum_lane_target_refusal_precedes_descriptor_fields_and_untagged_has_no_lane() {
    for mut module in [direct(), niche(), enum_module(definition(vec![vec![]]))] {
        module.target_info.as_mut().unwrap().triple = format!("i686-{}", "λ".repeat(1200));
        if let Some(desc) = module.enums[0].layout.as_mut() {
            desc.align = 0;
        }
        equal(&module);
    }
    let mut def = definition(vec![vec![Ty::Never]]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: 0,
        align: 1,
        variant_field_offsets: vec![vec![0]],
    });
    let mut module = enum_module(def);
    module.target_info.as_mut().unwrap().triple = "i686-unknown-linux-gnu".into();
    equal(&module);
}

#[test]
fn enum_duplicate_first_definition_by_value_cycle_and_size_overflow_match() {
    let mut module = direct();
    module.enums.push(definition(vec![]));
    equal(&module);
    module.enums[0] = definition(vec![vec![Ty::Enum(EnumId::new(7))]]);
    equal(&module);
    let mut module = enum_module(definition(vec![vec![Ty::Array(TyId::new(0), u64::MAX)]]));
    module.types.push(Ty::U128);
    equal(&module);
    let mut def = definition(vec![vec![]]);
    def.layout = Some(EnumLayoutDescriptor {
        encoding: EnumTagEncoding::Untagged,
        size: u64::MAX,
        align: 1,
        variant_field_offsets: vec![vec![]],
    });
    equal(&enum_module(def));
}

#[test]
fn least_fixpoint_inhabitedness_keeps_all_duplicates_missing_nodes_and_cycles() {
    let mut module = Module::new("inhabit_cycles");
    module.types = vec![
        Ty::Array(TyId::new(0), 1),
        Ty::Never,
        Ty::Refine(TyId::new(1), crate::PredId::new(0)),
    ];
    module.structs.push(structure(
        3,
        vec![field("self", Ty::Struct(StructId::new(3)), None)],
        0,
        1,
    ));
    module
        .structs
        .push(structure(4, vec![field("bottom", Ty::Never, None)], 0, 1));
    module
        .structs
        .push(structure(4, vec![field("live", Ty::Unit, None)], 0, 1));
    module.records.push(RecordDef {
        id: RecordId::new(5),
        name: "cycle".into(),
        fields: vec![
            field("self", Ty::Record(RecordId::new(5)), None),
            field("never", Ty::Never, None),
        ],
    });
    module
        .enums
        .push(EnumDef::new(EnumId::new(6), "empty", vec![]));
    module.enums.push(EnumDef::new(
        EnumId::new(8),
        "and",
        vec![
            variant(vec![Ty::Enum(EnumId::new(8)), Ty::Never]),
            variant(vec![Ty::Record(RecordId::new(5))]),
        ],
    ));
    let table = LayoutTable::new(&module);
    let mut observer = Observer::default();
    let mut session = ObservedSession::new(InterpretOptions::default(), &mut observer);
    for ty in [
        Ty::Never,
        Ty::Unit,
        Ty::Struct(StructId::new(3)),
        Ty::Struct(StructId::new(4)),
        Ty::Struct(StructId::new(99)),
        Ty::Record(RecordId::new(5)),
        Ty::Record(RecordId::new(99)),
        Ty::Enum(EnumId::new(6)),
        Ty::Enum(EnumId::new(8)),
        Ty::Array(TyId::new(0), 1),
        Ty::Array(TyId::new(1), 0),
        Ty::Array(TyId::new(1), 1),
        Ty::Refine(TyId::new(2), crate::PredId::new(0)),
        Ty::Tuple(vec![Ty::Unit, Ty::Never]),
        Ty::Ref(Box::new(Ty::Never)),
        Ty::Closure(ClosureTyId::new(99)),
    ] {
        assert_eq!(
            table
                .ty_is_uninhabited_observed(&ty, &mut session, site())
                .unwrap(),
            table.ty_is_uninhabited(&ty)
        );
    }
    for def in &module.enums {
        for variant in &def.variants {
            assert_eq!(
                table
                    .variant_is_uninhabited_observed(variant, &mut session, site())
                    .unwrap(),
                table.variant_is_uninhabited(variant)
            );
        }
    }
}
