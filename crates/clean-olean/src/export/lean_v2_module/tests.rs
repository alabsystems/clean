// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::import::{assemble_load_part, parse_load_module};
use crate::region::CompactedRegion;
use crate::TypedImportFlags;
use clean_kernel::{Expr, Reducibility};

const OFFICIAL: &[u8] =
    include_bytes!("../../../../../tests/fixtures/olean/v4.36.0/plain/StablePlain.olean");

fn theorem(name: Name, proof: Expr) -> ConstantInfo {
    ConstantInfo::new_with_reducibility(
        name,
        Vec::new(),
        Expr::const_str("True"),
        Some(proof),
        Reducibility::Opaque,
        ConstantKind::Theorem,
    )
}

#[test]
fn stable_split_module_keeps_public_stubs_and_private_proofs_in_their_views() {
    let header = OleanHeader::parse(OFFICIAL).unwrap();
    let module = Name::anon().str("Seal");
    let hidden = theorem(
        Name::anon()
            .str("_private")
            .str("Seal")
            .num(0)
            .str("Seal")
            .str("hidden"),
        Expr::const_str("True.intro"),
    );
    let exposed = theorem(
        module.clone().str("exportedProof"),
        Expr::const_(hidden.name.clone(), Vec::new()),
    );
    let declarations = [
        LeanV2ModuleDeclaration {
            info: &hidden,
            safety: DefinitionSafety::Safe,
            all: std::slice::from_ref(&hidden.name),
            visibility: LeanV2Visibility::Private,
            axioms: &[],
        },
        LeanV2ModuleDeclaration {
            info: &exposed,
            safety: DefinitionSafety::Safe,
            all: std::slice::from_ref(&exposed.name),
            visibility: LeanV2Visibility::ExportedAsAxiom,
            axioms: &[],
        },
    ];
    let imports = [false, true].map(|is_meta| TypedImport {
        module_name: Name::anon().str("Init"),
        flags: TypedImportFlags::LeanV2 {
            import_all: false,
            is_exported: true,
            is_meta,
        },
    });
    let native = write_lean_v2_module(
        &header,
        &module,
        &imports,
        &declarations,
        LeanV2ModuleOptions {
            is_module: true,
            namespaces: std::slice::from_ref(&module),
            emit_ir: true,
        },
    )
    .unwrap();
    let base = parse_load_module(native.base.clone()).unwrap();
    assert!(base.is_module);
    assert_eq!(base.typed_imports, imports);
    assert_eq!(base.const_names, [exposed.name.clone()]);
    assert_eq!(base.constants[0].kind, crate::ConstantKind::Axiom);
    assert_eq!(base.constants[0].value_ptr, 0);
    assert!(!native
        .base
        .windows(b"hidden".len())
        .any(|bytes| bytes == b"hidden"));

    let server = native.server.unwrap();
    let private = native.private.unwrap();
    let joined = assemble_load_part(&native.base, Some(&server), &private).unwrap();
    let region = CompactedRegion::new(&joined.bytes, joined.base_addr);
    let complete = region
        .read_module_data_from_ptr(joined.root_ptr, &private)
        .unwrap();
    assert_eq!(complete.constants.len(), 2);
    assert!(complete
        .constants
        .iter()
        .all(|constant| constant.kind == crate::ConstantKind::Theorem && constant.value.is_some()));
    assert!(complete.clean_payload.is_none());

    for (bytes, preceding) in [(&server, &native.base), (&private, &server)] {
        let address = OleanHeader::parse(bytes).unwrap().base_addr;
        let earlier_base = OleanHeader::parse(preceding).unwrap().base_addr;
        assert_eq!(
            address,
            (earlier_base + preceding.len() as u64 + 0xffff) & !0xffff
        );
    }

    let signature = native.ir_signature.unwrap();
    let body = native.ir.unwrap();
    let parsed_signature = parse_load_module(signature.clone()).unwrap();
    assert!(!parsed_signature.is_module);
    assert!(parsed_signature.typed_imports.is_empty());
    let joined = assemble_load_part(&signature, None, &body).unwrap();
    let ir = CompactedRegion::new(&joined.bytes, joined.base_addr);
    let entries = ir.ir_part_entries(joined.root_ptr).unwrap();
    assert!(entries.is_module);
    assert!(entries.get("Lean.IR.declMapExt").is_some());
    assert!(entries.get("Lean.regularInitAttr").is_some());
}
