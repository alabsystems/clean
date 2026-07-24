// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Item, ReceiverMode, RustType};
use super::{SourceError, SourceProgram};

#[test]
fn test_source_program_parses_trait_method_self_associated_type_signature() {
    let source = r#"
        trait Iterator {
            type Item;
            fn current(&self) -> Self::Item;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait method Self::Item signature should parse");

    let trait_def = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::TraitDef(def) if def.name == "Iterator" => Some(def),
            _ => None,
        })
        .expect("Iterator trait should be present");
    let method = trait_def
        .methods
        .iter()
        .find(|method| method.name == "current")
        .expect("current method should be present");

    assert_eq!(method.receiver, ReceiverMode::ByRef);
    assert!(
        method.params.is_empty(),
        "current should have no extra params"
    );
    assert_eq!(
        method.ret,
        RustType::TypeProjection {
            self_ty: Box::new(RustType::Named {
                name: "Self".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            }),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        }
    );
}

#[test]
fn test_source_program_parses_impl_method_self_associated_type_signature() {
    let source = r#"
        trait Iterator {
            type Item;
            fn current(&self) -> Self::Item;
        }

        struct Counter;

        impl Iterator for Counter {
            type Item = u32;

            fn current(&self) -> Self::Item {
                42u32
            }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("impl method Self::Item signature should parse");

    let impl_item = program
        .items()
        .iter()
        .find(
            |item| matches!(item, Item::Impl { trait_name: Some(name), .. } if name == "Iterator"),
        )
        .expect("Iterator impl should be present");
    let impl_items = match impl_item {
        Item::Impl { items, .. } => items,
        _ => panic!("expected impl item"),
    };
    let method = impl_items
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "current"))
        .expect("current impl method should be present");
    let ret = match method {
        Item::Fn { ret, .. } => ret,
        _ => panic!("expected function item"),
    };

    assert_eq!(
        ret,
        &RustType::TypeProjection {
            self_ty: Box::new(RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            }),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        }
    );
}

#[test]
fn test_source_program_parses_trait_method_returning_self() {
    let source = r#"
        trait Clonable {
            fn duplicate(&self) -> Self;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait method returning Self should parse");

    let trait_def = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::TraitDef(def) if def.name == "Clonable" => Some(def),
            _ => None,
        })
        .expect("Clonable trait should be present");
    let method = trait_def
        .methods
        .iter()
        .find(|method| method.name == "duplicate")
        .expect("duplicate method should be present");

    assert_eq!(method.receiver, ReceiverMode::ByRef);
    assert_eq!(
        method.ret,
        RustType::Named {
            name: "Self".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        }
    );
}

#[test]
fn test_source_program_parses_trait_method_with_self_parameter() {
    let source = r#"
        trait Merge {
            fn merge(self, other: Self) -> Self;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait method with Self param should parse");

    let trait_def = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::TraitDef(def) if def.name == "Merge" => Some(def),
            _ => None,
        })
        .expect("Merge trait should be present");
    let method = trait_def
        .methods
        .iter()
        .find(|method| method.name == "merge")
        .expect("merge method should be present");

    let self_placeholder = RustType::Named {
        name: "Self".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    };

    assert_eq!(method.receiver, ReceiverMode::ByValue);
    assert_eq!(method.params, vec![self_placeholder.clone()]);
    assert_eq!(method.ret, self_placeholder);
}

#[test]
fn test_source_program_parses_trait_method_returning_option_self() {
    let source = r#"
        trait TryClone {
            fn try_clone(&self) -> Option<Self>;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait method returning Option<Self> should parse");

    let trait_def = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::TraitDef(def) if def.name == "TryClone" => Some(def),
            _ => None,
        })
        .expect("TryClone trait should be present");
    let method = trait_def
        .methods
        .iter()
        .find(|method| method.name == "try_clone")
        .expect("try_clone method should be present");

    let self_placeholder = RustType::Named {
        name: "Self".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    };

    assert_eq!(
        method.ret,
        RustType::Option {
            inner: Box::new(self_placeholder),
        }
    );
}

#[test]
fn test_source_program_parses_trait_method_with_ref_self_param() {
    let source = r#"
        trait Comparable {
            fn compare(&self, other: &Self) -> bool;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait method with &Self param should parse");

    let trait_def = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::TraitDef(def) if def.name == "Comparable" => Some(def),
            _ => None,
        })
        .expect("Comparable trait should be present");
    let method = trait_def
        .methods
        .iter()
        .find(|method| method.name == "compare")
        .expect("compare method should be present");

    assert_eq!(method.receiver, ReceiverMode::ByRef);
    assert_eq!(method.params.len(), 1);
    match &method.params[0] {
        RustType::Reference { inner, .. } => {
            assert_eq!(
                inner.as_ref(),
                &RustType::Named {
                    name: "Self".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }
            );
        }
        other => panic!("expected &Self reference param, got {other:?}"),
    }
    assert_eq!(method.ret, RustType::Bool);
}

#[test]
fn test_source_program_rejects_self_projection_type_outside_trait_context() {
    let source = r#"
        fn project(_value: Self::Item) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let err =
        SourceProgram::parse(source).expect_err("top-level Self::Item type should fail closed");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "type");
            assert!(
                detail.contains("trait context"),
                "detail should mention the missing trait context, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}
