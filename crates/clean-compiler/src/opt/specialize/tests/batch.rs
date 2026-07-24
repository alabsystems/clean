// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Batch API, create_specialized_decl, and end-to-end specialization tests.

use super::*;

#[test]
fn test_specialize_all_empty() {
    let config = SpecConfig::default();
    let result = specialize_all(&[], &config);
    assert!(result.is_empty());
}

#[test]
fn test_specialize_all_single_decl_no_specialization() {
    use crate::lcnf::Param;

    let decl = Decl::new(
        name("foo"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("n"), nat_type())],
        Code::ret(fvar(1)),
        false,
    );

    let config = SpecConfig::default();
    let result = specialize_all(&[decl], &config);

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, name("foo"));
}

#[test]
fn test_specialize_all_preserves_multiple_decls() {
    use crate::lcnf::Param;

    let decl1 = Decl::new(
        name("foo"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("n"), nat_type())],
        Code::ret(fvar(1)),
        false,
    );

    let decl2 = Decl::new(
        name("bar"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(10), name("m"), nat_type())],
        Code::ret(fvar(10)),
        false,
    );

    let config = SpecConfig::default();
    let result = specialize_all(&[decl1, decl2], &config);

    assert!(result.len() >= 2);
    assert!(result.iter().any(|d| d.name == name("foo")));
    assert!(result.iter().any(|d| d.name == name("bar")));
}

#[test]
fn test_specialize_all_disabled() {
    use crate::lcnf::Param;

    let decl = Decl::new(
        name("foo"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("n"), nat_type())],
        Code::let_bind(
            LetDecl::new(fvar(2), name("_1"), nat_type(), LetValue::nat(42)),
            Code::ret(fvar(2)),
        ),
        false,
    );

    let config = SpecConfig {
        specialize_instances: false,
        specialize_higher_order: false,
        max_depth: 0,
    };
    let result = specialize_all(&[decl], &config);

    assert_eq!(result.len(), 1);
    assert_eq!(result[0].name, name("foo"));
}

#[test]
fn test_specialize_all_with_extern() {
    let decl = Decl {
        name: name("extern_fn"),
        level_params: vec![],
        ty: nat_type(),
        params: vec![],
        body: DeclValue::Extern(crate::lcnf::ExternAttr { entries: vec![] }),
        recursive: false,
    };

    let config = SpecConfig::default();
    let result = specialize_all(&[decl], &config);

    assert_eq!(result.len(), 1);
    assert!(matches!(result[0].body, DeclValue::Extern(_)));
}

#[test]
fn test_create_specialized_decl_filters_ground_params() {
    use crate::lcnf::Param;

    let original = Decl::new(
        name("original_fn"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(1), name("inst"), nat_type()),
            Param::new(fvar(2), name("x"), nat_type()),
        ],
        Code::ret(fvar(2)),
        false,
    );

    let ground_args = vec![SpecKey::Ground(GroundValue::Lit(42)), SpecKey::Erased];
    let ground_values = vec![Some(LetValue::nat(42)), None];
    let original_code = Code::ret(fvar(2));

    let result = create_specialized_decl(
        &original,
        &name("original_fn_spec_0"),
        &ground_args,
        &ground_values,
        &original_code,
    );

    let spec_decl = result.expect("invariant: specialization should produce a decl");
    assert_eq!(spec_decl.name, name("original_fn_spec_0"));
    assert_eq!(spec_decl.params.len(), 1);
    assert_eq!(spec_decl.params[0].fvar_id, fvar(2));
}

#[test]
fn test_create_specialized_decl_all_ground() {
    use crate::lcnf::Param;

    let original = Decl::new(
        name("all_ground"),
        vec![],
        nat_type(),
        vec![
            Param::new(fvar(1), name("a"), nat_type()),
            Param::new(fvar(2), name("b"), nat_type()),
        ],
        Code::ret(fvar(1)),
        false,
    );

    let ground_args = vec![
        SpecKey::Ground(GroundValue::Lit(1)),
        SpecKey::Ground(GroundValue::Lit(2)),
    ];
    let ground_values = vec![Some(LetValue::nat(1)), Some(LetValue::nat(2))];
    let original_code = Code::ret(fvar(1));

    let result = create_specialized_decl(
        &original,
        &name("all_ground_spec"),
        &ground_args,
        &ground_values,
        &original_code,
    );

    let spec_decl = result.expect("invariant: all-ground specialization produces a decl");
    assert_eq!(spec_decl.params.len(), 0);
}

#[test]
fn test_create_specialized_decl_preserves_metadata() {
    use crate::lcnf::Param;

    let original = Decl {
        name: name("meta_fn"),
        level_params: vec![name("u")],
        ty: nat_type(),
        params: vec![Param::new(fvar(1), name("x"), nat_type())],
        body: DeclValue::Code(Box::new(Code::ret(fvar(1)))),
        recursive: true,
    };

    let ground_args = vec![SpecKey::Erased];
    let ground_values = vec![None];
    let original_code = Code::ret(fvar(1));

    let result = create_specialized_decl(
        &original,
        &name("meta_fn_spec"),
        &ground_args,
        &ground_values,
        &original_code,
    );

    let spec_decl = result.expect("invariant: metadata-preserving spec produces a decl");
    assert_eq!(spec_decl.level_params.len(), 1);
    assert!(spec_decl.recursive);
}

#[test]
fn test_specialize_all_generates_specialized_decl() {
    use crate::lcnf::Param;

    let foo_decl = Decl::new(
        name("foo"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("inst"), nat_type())],
        Code::ret(fvar(1)),
        false,
    );

    let bar_decl = Decl::new(
        name("bar"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(10), name("_1"), nat_type(), LetValue::nat(42)),
            Code::let_bind(
                LetDecl::new(
                    fvar(11),
                    name("_2"),
                    nat_type(),
                    LetValue::Const {
                        name: name("foo"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(10))],
                    },
                ),
                Code::ret(fvar(11)),
            ),
        ),
        false,
    );

    let config = SpecConfig::default();
    let result = specialize_all(&[foo_decl, bar_decl], &config);

    assert!(
        result.len() >= 3,
        "Expected at least 3 decls (foo, bar, specialized), got {}",
        result.len()
    );
    assert!(result.iter().any(|d| d.name == name("foo")));
    assert!(result.iter().any(|d| d.name == name("bar")));
    assert!(
        result.iter().any(|d| d.name.to_string().contains("_spec")),
        "Expected specialized declaration with '_spec' in name"
    );
}

#[test]
fn test_specialize_all_rewrites_call_site() {
    use crate::lcnf::Param;

    let foo_decl = Decl::new(
        name("foo"),
        vec![],
        nat_type(),
        vec![Param::new(fvar(1), name("inst"), nat_type())],
        Code::ret(fvar(1)),
        false,
    );

    let bar_decl = Decl::new(
        name("bar"),
        vec![],
        nat_type(),
        vec![],
        Code::let_bind(
            LetDecl::new(fvar(10), name("_1"), nat_type(), LetValue::nat(100)),
            Code::let_bind(
                LetDecl::new(
                    fvar(11),
                    name("_2"),
                    nat_type(),
                    LetValue::Const {
                        name: name("foo"),
                        levels: vec![],
                        args: vec![Arg::FVar(fvar(10))],
                    },
                ),
                Code::ret(fvar(11)),
            ),
        ),
        false,
    );

    let config = SpecConfig::default();
    let result = specialize_all(&[foo_decl, bar_decl], &config);

    let bar_transformed = result
        .iter()
        .find(|d| d.name == name("bar"))
        .expect("invariant: bar should be in result");

    let DeclValue::Code(code) = &bar_transformed.body else {
        unreachable!("invariant: bar has Code body, not Extern");
    };

    let call_name =
        extract_first_const_call(code).expect("invariant: bar should still contain a const call");
    assert!(
        call_name.contains("_spec"),
        "Call should be rewritten to specialized version, got: {}",
        call_name
    );
}
