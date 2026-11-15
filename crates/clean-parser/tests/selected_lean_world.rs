// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use clean_parser::{parse_file, parse_file_in_world, LeanWorld, SurfaceDecl, Visibility};

#[test]
fn public_parser_selects_only_the_measured_variable_visibility_world() {
    let source = "private variable (x : Nat)\npublic def usesPrivate : Nat := x\n";
    assert!(parse_file(source).is_err());
    for world in LeanWorld::ALL {
        let result = parse_file_in_world(source, world);
        if world != LeanWorld::Lean436Rc2 {
            assert!(result.is_err(), "{world}");
            continue;
        }
        let decls = result.expect("qualified rc2 accepts private variable before public def");
        assert!(matches!(
            decls.as_slice(),
            [
                SurfaceDecl::Variable {
                    visibility: Some(Visibility::Private),
                    ..
                },
                SurfaceDecl::Def { .. }
            ]
        ));
    }
    for unknown in ["v4.31.0", "v4.36.0", "v4.99.0"] {
        assert!(unknown.parse::<LeanWorld>().is_err(), "{unknown}");
    }
}

#[test]
fn selected_parser_keeps_variable_modifier_and_scope_provenance() {
    for (modifier, visibility) in [
        ("private", Visibility::Private),
        ("public", Visibility::Public),
    ] {
        let source =
            format!("{modifier} variable (x : Nat) in\npublic def usesVariable : Nat := x\n");
        let decls =
            parse_file_in_world(&source, LeanWorld::Lean436Rc2).expect("native rc2 accepts");
        let [SurfaceDecl::Section { decls, .. }] = decls.as_slice() else {
            panic!("variable-in scope")
        };
        assert!(
            matches!(&decls[0], SurfaceDecl::Variable { visibility: Some(found), .. } if *found == visibility)
        );
    }
    let decls = parse_file_in_world("variable (x : Nat)", LeanWorld::Lean436Rc2).unwrap();
    assert!(matches!(
        &decls[0],
        SurfaceDecl::Variable {
            visibility: None,
            ..
        }
    ));
}

#[test]
fn selecting_a_world_keeps_old_modifier_and_first_error_refusals() {
    for source in [
        "protected variable (x : Nat)",
        "public private variable (x : Nat)",
        "@[simp] private variable (x : Nat)",
        "/-- a -/ /-- b -/ def later := 1",
    ] {
        for world in LeanWorld::ALL {
            assert!(
                parse_file_in_world(source, world).is_err(),
                "{world}: {source}"
            );
        }
    }
}
