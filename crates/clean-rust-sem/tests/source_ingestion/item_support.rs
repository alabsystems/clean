// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};
use clean_rust_sem::expr::Item;
use clean_rust_sem::RustType;

#[test]
fn test_source_program_rejects_negative_trait_impl() {
    let source = r#"
        struct Foo;

        impl !Send for Foo {}

        fn main() -> u32 {
            42u32
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("negative trait impl should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "impl");
            assert!(
                detail.contains("negative"),
                "detail should mention negative trait impl, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_skips_use_declarations() {
    let source = r#"
        use std::collections::HashMap;
        use std::io;

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("use declarations should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_skips_block_level_use() {
    let source = r#"
        fn main() -> u32 {
            use std::io;
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-level use should be skipped");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_parses_union_definition_and_init() {
    let source = r#"
        union IntOrFloat {
            i: u32,
            f: u32,
        }

        fn main() -> u32 {
            let _u = IntOrFloat { i: 42u32 };
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("union definition and init should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_parses_generic_union() {
    let source = r#"
        union Foo<T> {
            a: T,
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("generic union should parse");

    match &program.items()[0] {
        Item::Union {
            fields,
            type_params,
            ..
        } => {
            assert_eq!(type_params.len(), 1);
            assert_eq!(type_params[0].name, "T");
            assert_eq!(fields.len(), 1);
            match &fields[0].1 {
                RustType::TypeParam(type_var) => {
                    assert_eq!(type_var.name.as_deref(), Some("T"));
                }
                other => panic!("expected union field type param, got {other:?}"),
            }
        }
        other => panic!("expected Union, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_dyn_trait_type() {
    let source = r#"
        fn accept_dyn(x: &dyn Display) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("dyn trait type should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_parses_impl_trait_return_type() {
    let source = r#"
        fn make_thing() -> impl Display {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("impl trait return type should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_parses_dyn_trait_with_lifetime() {
    let source = r#"
        fn accept_dyn(x: &(dyn Display + 'static)) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("dyn trait with lifetime should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
