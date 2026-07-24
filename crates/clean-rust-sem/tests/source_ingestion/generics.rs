// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::expr::{Expr, Item, Stmt};
use clean_rust_sem::types::{ConstGenericArg, UintType};
use clean_rust_sem::{RustType, SourceProgram};

fn assert_type_param(ty: &RustType, expected_name: &str) {
    match ty {
        RustType::TypeParam(type_var) => {
            assert_eq!(type_var.name.as_deref(), Some(expected_name));
        }
        other => panic!("expected TypeParam({expected_name}), got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_struct() {
    let source = r#"
        struct Wrapper<T> {
            inner: T,
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Struct {
            name,
            fields,
            type_params,
            ..
        } => {
            assert_eq!(name, "Wrapper");
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "inner");
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
            assert!(type_params[0].bounds.is_empty());
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_struct_with_bounds() {
    let source = r#"
        struct Container<T: Clone + Default> {
            value: T,
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Struct { type_params, .. } => {
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
            assert_eq!(type_params[0].bounds, vec!["Clone", "Default"]);
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_enum() {
    let source = r#"
        enum MyOption<T> {
            Some(T),
            None,
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Enum {
            name,
            variants,
            type_params,
            ..
        } => {
            assert_eq!(name, "MyOption");
            assert_eq!(variants.len(), 2);
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
        }
        other => panic!("expected Enum, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_enum_multiple_params() {
    let source = r#"
        enum MyResult<T, E> {
            Ok(T),
            Err(E),
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Enum { type_params, .. } => {
            assert_eq!(type_params.len(), 2);
            assert_eq!(type_params[0].name, "T");
            assert_eq!(type_params[1].name, "E");
        }
        other => panic!("expected Enum, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_function() {
    let source = r#"
        fn identity<T>(x: T) -> T {
            x
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Fn {
            name, type_params, ..
        } => {
            assert_eq!(name, "identity");
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_function_with_where_clause() {
    let source = r#"
        fn print_it<T>(x: T) where T: Display {
            x
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Fn { type_params, .. } => {
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
            assert_eq!(type_params[0].bounds, vec!["Display"]);
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_impl_block() {
    let source = r#"
        struct Wrapper<T> {
            inner: T,
        }
        impl<T> Wrapper<T> {
            fn new(inner: T) -> Wrapper<T> {
                Wrapper { inner: inner }
            }
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let impl_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::Impl { .. }))
        .expect("should have Impl item");
    match impl_item {
        Item::Impl {
            type_params, items, ..
        } => {
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
            assert_eq!(items.len(), 1);
        }
        _ => unreachable!(),
    }
}

#[test]
fn test_source_program_parses_lifetime_params_without_error() {
    let source = r#"
        struct Ref<'a, T> {
            data: &'a T,
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Struct { type_params, .. } => {
            // Lifetime params are accepted but only type params appear
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_const_generic_struct() {
    let source = r#"
        struct FixedArray<const N: usize> {
            data: [u8; N],
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Struct {
            name,
            fields,
            type_params,
            const_params,
            ..
        } => {
            assert_eq!(name, "FixedArray");
            assert!(type_params.is_empty());
            assert_eq!(const_params.len(), 1);
            assert_eq!(const_params[0].name, "N");
            assert_eq!(const_params[0].ty, RustType::Uint(UintType::Usize));
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].0, "data");
            match &fields[0].1 {
                RustType::Array { element, len } => {
                    assert_eq!(element.as_ref(), &RustType::Uint(UintType::U8));
                    assert_eq!(len, &ConstGenericArg::Param("N".to_string()));
                }
                other => panic!("expected array field, got {other:?}"),
            }
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_method_in_impl() {
    let source = r#"
        struct Converter;
        impl Converter {
            fn convert<T>(x: T) -> T {
                x
            }
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let impl_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::Impl { .. }))
        .expect("should have Impl item");
    match impl_item {
        Item::Impl { items, .. } => {
            let method = &items[0];
            match method {
                Item::Fn {
                    name, type_params, ..
                } => {
                    assert_eq!(name, "convert");
                    assert_eq!(type_params.len(), 1);
                    assert_eq!(type_params[0].name, "T");
                }
                other => panic!("expected Fn, got {other:?}"),
            }
        }
        _ => unreachable!(),
    }
}

#[test]
fn test_source_program_nongeneric_items_have_empty_type_params() {
    let source = r#"
        struct Point {
            x: i32,
            y: i32,
        }
        fn add(a: i32, b: i32) -> i32 {
            a + b
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    match &program.items()[0] {
        Item::Struct { type_params, .. } => assert!(type_params.is_empty()),
        other => panic!("expected Struct, got {other:?}"),
    }
    match &program.items()[1] {
        Item::Fn { type_params, .. } => assert!(type_params.is_empty()),
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_bounds_inline_and_where_clause() {
    let source = r#"
        fn process<T: Clone>(x: T) -> T where T: Default {
            x
        }
    "#;
    let program = SourceProgram::parse(source).unwrap();
    let item = &program.items()[0];
    match item {
        Item::Fn { type_params, .. } => {
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
            assert!(type_params[0].bounds.contains(&"Clone".to_string()));
            assert!(type_params[0].bounds.contains(&"Default".to_string()));
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn test_source_program_lowers_generic_struct_field_type_to_type_param() {
    let source = r#"
        struct Wrapper<T> {
            inner: T,
        }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    match &program.items()[0] {
        Item::Struct { fields, .. } => {
            assert_eq!(fields.len(), 1);
            assert_type_param(&fields[0].1, "T");
        }
        other => panic!("expected Struct, got {other:?}"),
    }
}

#[test]
fn test_source_program_lowers_generic_function_signature_and_body_annotations() {
    let source = r#"
        fn identity<T>(value: T) -> T {
            let shadow: T = value;
            shadow
        }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    match &program.items()[0] {
        Item::Fn {
            params, ret, body, ..
        } => {
            assert_eq!(params.len(), 1);
            assert_type_param(&params[0].1, "T");
            assert_type_param(ret, "T");

            let Expr::Block { stmts, .. } = body else {
                panic!("expected function body block, got {body:?}");
            };
            let Some(Stmt::Let {
                ty: Some(let_ty), ..
            }) = stmts.first()
            else {
                panic!("expected typed let statement in function body, got {stmts:?}");
            };
            assert_type_param(let_ty, "T");
        }
        other => panic!("expected Fn, got {other:?}"),
    }
}

#[test]
fn test_source_program_lowers_impl_and_method_generic_references() {
    let source = r#"
        struct Wrapper<T> {
            value: T,
        }

        impl<T> Wrapper<T> {
            fn replace<U>(self, value: T, other: U) -> Wrapper<T> {
                Wrapper { value: value }
            }
        }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let impl_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::Impl { .. }))
        .expect("expected impl item");

    match impl_item {
        Item::Impl { self_ty, items, .. } => {
            match self_ty {
                RustType::Named {
                    name, type_args, ..
                } => {
                    assert_eq!(name, "Wrapper");
                    assert_eq!(type_args.len(), 1);
                    assert_type_param(&type_args[0], "T");
                }
                other => panic!("expected named impl self type, got {other:?}"),
            }

            let method = items
                .iter()
                .find(|item| matches!(item, Item::Fn { name, .. } if name == "replace"))
                .expect("expected replace method");
            match method {
                Item::Fn { params, ret, .. } => {
                    assert_eq!(params.len(), 3);
                    assert_type_param(&params[1].1, "T");
                    assert_type_param(&params[2].1, "U");
                    match ret {
                        RustType::Named {
                            name, type_args, ..
                        } => {
                            assert_eq!(name, "Wrapper");
                            assert_eq!(type_args.len(), 1);
                            assert_type_param(&type_args[0], "T");
                        }
                        other => panic!("expected named method return type, got {other:?}"),
                    }
                }
                other => panic!("expected Fn, got {other:?}"),
            }
        }
        other => panic!("expected Impl, got {other:?}"),
    }
}

#[test]
fn test_source_program_nested_items_do_not_inherit_outer_generic_params() {
    let source = r#"
        fn outer<T>(value: T) -> T {
            struct Inner {
                value: T,
            }

            value
        }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let body = match &program.items()[0] {
        Item::Fn { body, .. } => body,
        other => panic!("expected Fn, got {other:?}"),
    };
    let Expr::Block { stmts, .. } = body else {
        panic!("expected function body block, got {body:?}");
    };
    let Some(Stmt::Item(Item::Struct { fields, .. })) = stmts.first() else {
        panic!("expected nested struct item, got {stmts:?}");
    };

    match &fields[0].1 {
        RustType::Named {
            name,
            type_args,
            lifetime_args,
            ..
        } => {
            assert_eq!(name, "T");
            assert!(type_args.is_empty());
            assert!(lifetime_args.is_empty());
        }
        other => panic!("expected nested item field type to stay unresolved, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_trait_definition() {
    let source = r#"
        trait Convert<T> {
            fn convert(&self) -> T;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let trait_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(_)))
        .expect("expected TraitDef item");

    match trait_item {
        Item::TraitDef(def) => {
            assert_eq!(def.name, "Convert");
            assert_eq!(def.type_params.len(), 1);
            assert_eq!(def.type_params[0].name, "T");
            assert_eq!(def.methods.len(), 1);
            assert_eq!(def.methods[0].name, "convert");
            assert_type_param(&def.methods[0].ret, "T");
        }
        other => panic!("expected TraitDef, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_trait_with_bounds() {
    let source = r#"
        trait Transform<T: Clone, U: Clone + Send> {
            fn transform(&self, input: T) -> U;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let trait_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(_)))
        .expect("expected TraitDef item");

    match trait_item {
        Item::TraitDef(def) => {
            assert_eq!(def.name, "Transform");
            assert_eq!(def.type_params.len(), 2);
            assert_eq!(def.type_params[0].name, "T");
            assert_eq!(def.type_params[0].bounds, vec!["Clone"]);
            assert_eq!(def.type_params[1].name, "U");
            assert_eq!(def.type_params[1].bounds, vec!["Clone", "Send"]);
            assert_eq!(def.methods.len(), 1);
            assert_type_param(&def.methods[0].params[0], "T");
            assert_type_param(&def.methods[0].ret, "U");
        }
        other => panic!("expected TraitDef, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_trait_with_where_clause() {
    let source = r#"
        trait Container<T> where T: Clone {
            fn get(&self) -> T;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let trait_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(_)))
        .expect("expected TraitDef item");

    match trait_item {
        Item::TraitDef(def) => {
            assert_eq!(def.name, "Container");
            assert_eq!(def.type_params.len(), 1);
            assert_eq!(def.type_params[0].name, "T");
            assert!(def.type_params[0].bounds.contains(&"Clone".to_string()));
            assert_type_param(&def.methods[0].ret, "T");
        }
        other => panic!("expected TraitDef, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_generic_trait_method() {
    let source = r#"
        trait Mapper {
            fn map<B>(&self, f: B) -> B;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let trait_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(_)))
        .expect("expected TraitDef item");

    match trait_item {
        Item::TraitDef(def) => {
            assert_eq!(def.name, "Mapper");
            assert!(def.type_params.is_empty());
            assert_eq!(def.methods.len(), 1);
            assert_eq!(def.methods[0].name, "map");
            assert_eq!(def.methods[0].type_params.len(), 1);
            assert_eq!(def.methods[0].type_params[0].name, "B");
            assert_type_param(&def.methods[0].params[0], "B");
            assert_type_param(&def.methods[0].ret, "B");
        }
        other => panic!("expected TraitDef, got {other:?}"),
    }
}

#[test]
fn test_source_program_preserves_generic_trait_method_bounds() {
    let source = r#"
        trait Mapper<T> {
            fn map<B: Clone>(self, input: T, f: B) -> B where B: Default;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let trait_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(_)))
        .expect("expected TraitDef item");

    match trait_item {
        Item::TraitDef(def) => {
            assert_eq!(def.name, "Mapper");
            assert_eq!(def.type_params.len(), 1);
            assert_eq!(def.type_params[0].name, "T");
            assert_eq!(def.methods.len(), 1);
            assert_eq!(def.methods[0].name, "map");
            assert_eq!(def.methods[0].type_params.len(), 1);
            assert_eq!(def.methods[0].type_params[0].name, "B");
            assert!(def.methods[0].type_params[0]
                .bounds
                .contains(&"Clone".to_string()));
            assert!(def.methods[0].type_params[0]
                .bounds
                .contains(&"Default".to_string()));
            assert_type_param(&def.methods[0].params[0], "T");
            assert_type_param(&def.methods[0].params[1], "B");
            assert_type_param(&def.methods[0].ret, "B");
        }
        other => panic!("expected TraitDef, got {other:?}"),
    }
}

#[test]
fn test_source_program_nongeneric_trait_has_empty_type_params() {
    let source = r#"
        trait Speaker {
            fn speak(&self) -> u32;
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).unwrap();
    let trait_item = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(_)))
        .expect("expected TraitDef item");

    match trait_item {
        Item::TraitDef(def) => {
            assert_eq!(def.name, "Speaker");
            assert!(def.type_params.is_empty());
            assert!(def.methods[0].type_params.is_empty());
        }
        other => panic!("expected TraitDef, got {other:?}"),
    }
}
