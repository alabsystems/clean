// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(all(feature = "parser", feature = "binary"))]

use trust_ir::parser::{parse_module, parse_template};
use trust_ir::proof::ProofDigest;
use trust_ir::template::{TEMPLATE_BODY_NAME, Template, TemplateHeader, TemplateParam};
use trust_ir::ty::{
    EnumDef, EnumTagRepr, EnumVariant, FieldDef, StructDef, StructRepr, TypeOrigin,
};
use trust_ir::{
    BlockG, BlockId, EnumId, FuncId, FuncTyG, FunctionG, InstG, InstrNodeG, Module, ParamId,
    StructId, TemplateRef, Ty, TyG, TyId, ValueId,
};

fn nominals() -> Module {
    let mut module = Module::new("nominal_text");
    module.add_struct(StructDef {
        id: StructId::new(7),
        name: "Pair".into(),
        fields: vec![
            FieldDef {
                name: "small".into(),
                ty: Ty::U8,
                offset: Some(0),
            },
            FieldDef {
                name: "wide".into(),
                ty: Ty::U64,
                offset: Some(8),
            },
        ],
        size: Some(16),
        align: Some(8),
        repr: StructRepr::C,
        origin: Some(TypeOrigin::Rust {
            stable_crate_id: 17,
            def_path_hash: [3; 16],
            args_digest: ProofDigest::sha256_domain("nominal_text.arguments", b"actual-input"),
        }),
    });
    module.add_enum(EnumDef {
        id: EnumId::new(9),
        name: "Choice".into(),
        variants: vec![
            EnumVariant {
                name: "Empty".into(),
                fields: vec![],
                field_names: vec![],
            },
            EnumVariant {
                name: "Value".into(),
                fields: vec![Ty::U16],
                field_names: vec!["value".into()],
            },
        ],
        discriminants: vec![Some(2), Some(4)],
        repr: Some(EnumTagRepr::U8),
        layout: None,
        origin: Some(TypeOrigin::Clean {
            decl: "Fixture.Choice".into(),
            env_digest: ProofDigest::sha256_domain("nominal_text.environment", b"actual-input"),
        }),
    });
    module
}

fn template() -> Template {
    let mut ground = nominals();
    for row in &mut ground.structs {
        row.origin = None;
    }
    for row in &mut ground.enums {
        row.origin = None;
    }
    let mut module = ground
        .try_map_level(&mut |ty| Ok::<_, ()>(ty.embed()), &mut |constant, _| {
            Ok(constant.embed())
        })
        .unwrap();
    let param = TyG::Ext(TemplateRef::Param(ParamId::new(0)));
    let signature = module
        .add_func_type(FuncTyG {
            abi: None,
            params: vec![param.clone()],
            returns: vec![param.clone()],
            is_vararg: false,
        })
        .unwrap();
    let mut function = FunctionG::new(
        FuncId::new(0),
        TEMPLATE_BODY_NAME,
        signature,
        BlockId::new(0),
    );
    let mut block = BlockG::new(BlockId::new(0)).with_param(ValueId::new(0), param);
    block.body.push(InstrNodeG::new(InstG::Return {
        values: vec![ValueId::new(0)],
    }));
    function.blocks.push(block);
    module.functions.push(function);
    Template {
        header: TemplateHeader {
            identity: "fixture.nominal.text".into(),
            params: vec![TemplateParam::Type],
            holes: vec![],
        },
        module,
    }
}

#[test]
fn nominal_text_preserves_complete_r_rows_and_wire() {
    let original = nominals();
    let parsed = parse_module(&original.to_string()).unwrap();
    assert_eq!(parsed, original);
    assert_eq!(
        trust_ir::binary::serialize_module(&parsed).unwrap(),
        trust_ir::binary::serialize_module(&original).unwrap()
    );
    assert_eq!(parsed.structs[0].id, StructId::new(7));
    assert_eq!(parsed.enums[0].id, EnumId::new(9));
}

#[test]
fn nominal_text_embeds_ground_rows_in_s_and_refuses_direct_extensions() {
    let original = template();
    original.check_structure().unwrap();
    let text = original.to_string();
    assert_eq!(parse_template(&text).unwrap(), original);
    for ground in ["u64", "u16"] {
        let generic = text.replace(ground, "$0");
        assert_ne!(generic, text);
        assert!(parse_template(&generic).is_err());
    }
}

#[test]
fn nominal_text_still_refuses_generic_fields_through_a_type_row() {
    let mut generic = template();
    generic
        .module
        .types
        .push(TyG::Ext(TemplateRef::Param(ParamId::new(0))));
    generic.module.structs[0].fields[1].ty = TyG::Array(TyId::new(0), 3);
    assert!(generic.check_structure().is_err());
    assert!(parse_template(&generic.to_string()).is_err());
}
