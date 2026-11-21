// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use clean_olean::coq_vo::{
    constr::Constr, read_local_definition, vo_parser::VoObjFile, DefinitionBody,
};

const OBJECT: &[u8] = include_bytes!("fixtures/coq-8.20/LocalDefinition.vo");
const LIBRARY: &str = "LocalDefinition";

#[test]
fn read_the_actual_selected_local_body_and_type() {
    let definition =
        read_local_definition(OBJECT, LIBRARY, "LocalDefinition.Profile.endian").unwrap();
    assert_eq!(definition.kind, DefinitionBody::Transparent);
    assert_eq!(definition.qualified, "LocalDefinition.Profile.endian");
    assert_eq!(definition.library, LIBRARY);
    assert!(std::ptr::eq(definition.object, OBJECT));
    assert!(matches!(definition.ty, Constr::Ind(_)));
    assert!(matches!(definition.body, Constr::Construct(_)));

    let proof = read_local_definition(OBJECT, LIBRARY, "LocalDefinition.target_endian").unwrap();
    assert_eq!(proof.kind, DefinitionBody::LocalQed);
    assert!(matches!(proof.ty, Constr::App(_, _)));
    assert!(matches!(proof.body, Constr::App(_, _)));
    let another = read_local_definition(OBJECT, LIBRARY, "LocalDefinition.target_on").unwrap();
    assert_eq!(another.kind, DefinitionBody::LocalQed);
    assert_ne!(another.ty, proof.ty);
    assert_ne!(another.body, proof.body);
}

#[test]
fn selected_names_and_real_proof_bodies_are_mandatory() {
    for (library, name) in [
        ("Different", "Different.target_endian"),
        (LIBRARY, "Other.target_endian"),
        (LIBRARY, "LocalDefinition.Profile.missing"),
        (LIBRARY, "LocalDefinition.Profile"),
        (LIBRARY, "LocalDefinition.type_only"),
        (LIBRARY, "LocalDefinition.ProfileAlias.endian"),
        (LIBRARY, "LocalDefinition.T.i"),
        (LIBRARY, "LocalDefinition.WithArgument.copy"),
    ] {
        assert!(
            read_local_definition(OBJECT, library, name).is_err(),
            "{name}"
        );
    }

    // Rename just the opaque table's directory entry. The library's original
    // Qed declaration and its type are still present.
    let mut no_opaque_table = OBJECT.to_vec();
    let directory = u64::from_be_bytes(OBJECT[8..16].try_into().unwrap()) as usize;
    let name = no_opaque_table[directory..]
        .windows(7)
        .position(|s| s == b"opaques")
        .unwrap();
    no_opaque_table[directory + name] = b'x';
    let object = VoObjFile::parse(&no_opaque_table).unwrap();
    assert!(object.segment("library").is_some());
    assert!(object.segment("opaques").is_none());
    assert!(
        read_local_definition(&no_opaque_table, LIBRARY, "LocalDefinition.Profile.endian").is_ok()
    );
    assert!(
        read_local_definition(&no_opaque_table, LIBRARY, "LocalDefinition.target_endian").is_err()
    );
}
