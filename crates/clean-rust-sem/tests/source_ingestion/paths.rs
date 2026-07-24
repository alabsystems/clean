// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};

#[test]
fn test_source_program_runs_tuple_enum_variant_match() {
    let source = r#"
        enum Maybe {
            Nothing,
            Just(u32),
        }

        fn main() -> u32 {
            let value = Maybe::Just(41u32);
            match value {
                Maybe::Nothing => 0u32,
                Maybe::Just(inner) => inner + 1u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("enum source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_qself_tuple_enum_variant_match() {
    let source = r#"
        enum Maybe {
            Nothing,
            Just(u32),
        }

        fn main() -> u32 {
            let value = <Maybe>::Just(41u32);
            match value {
                Maybe::Nothing => 0u32,
                Maybe::Just(inner) => inner + 1u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("qself enum source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_unit_enum_variant_path() {
    let source = r#"
        enum Flag {
            Ready,
        }

        fn main() -> u32 {
            match Flag::Ready {
                Flag::Ready => 42u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("unit enum source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_qself_unit_enum_variant_path() {
    let source = r#"
        enum Flag {
            Ready,
        }

        fn main() -> u32 {
            match <Flag>::Ready {
                Flag::Ready => 42u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("qself unit enum path should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_struct_enum_variant_match() {
    let source = r#"
        enum Packet {
            Data { value: u32 },
        }

        fn main() -> u32 {
            match (Packet::Data { value: 42u32 }) {
                Packet::Data { value } => value,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("struct enum source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_resolves_associated_constant_u32_max() {
    let source = r#"
        fn main() -> u32 {
            u32::MAX
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("u32::MAX should parse as associated constant");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(u32::MAX)));
}

#[test]
fn test_source_program_rejects_unknown_qualified_path_expression() {
    let source = r#"
        fn main() -> u32 {
            Foo::BAR
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("unknown qualified path should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "path expression");
            assert!(
                detail.contains("Foo::BAR") && detail.contains("known top-level enum"),
                "detail should explain the unknown qualified path, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_runs_inherent_associated_function_call() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }

        fn main() -> u32 {
            let counter = Counter::new();
            counter.value
        }
    "#;

    let program = SourceProgram::parse(source).expect("associated function syntax should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_enum_inherent_associated_function_call() {
    let source = r#"
        enum Flag {
            Ready,
        }

        impl Flag {
            fn ready() -> Flag {
                Flag::Ready
            }
        }

        fn main() -> u32 {
            match Flag::ready() {
                Flag::Ready => 42u32,
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("enum associated function syntax should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_qualified_associated_function_ignores_same_named_free_function() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }

        fn new() -> Counter {
            Counter { value: 7u32 }
        }

        fn main() -> u32 {
            let counter = Counter::new();
            counter.value
        }
    "#;

    let program = SourceProgram::parse(source).expect("qualified associated function should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_rejects_unknown_qualified_call_expression() {
    let source = r#"
        fn main() -> u32 {
            util::build()
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("unknown qualified call should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "call expression");
            assert!(
                detail.contains("util::build") && detail.contains("known nominal type"),
                "detail should explain the unsupported qualified call, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_rejects_unknown_enum_variant_path_expression() {
    let source = r#"
        enum Flag {
            Ready,
        }

        fn main() -> Flag {
            Flag::Missing
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("unknown enum variant path should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "path expression");
            assert!(
                detail.contains("Flag::Missing") && detail.contains("known top-level enum variant"),
                "detail should explain the unsupported enum variant path, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_runs_tuple_enum_variant_constructor_path_value() {
    let source = r#"
        enum Maybe {
            Just(u32),
        }

        fn main() -> u32 {
            let ctor = Maybe::Just;
            match ctor(41u32) {
                Maybe::Just(inner) => inner + 1u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("tuple enum variant path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_qself_tuple_enum_variant_constructor_path_value() {
    let source = r#"
        enum Maybe {
            Just(u32),
        }

        fn main() -> u32 {
            let ctor = <Maybe>::Just;
            match ctor(41u32) {
                Maybe::Just(inner) => inner + 1u32,
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("qself tuple enum variant path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_rejects_struct_enum_variant_path_expression() {
    let source = r#"
        enum Maybe {
            Just { value: u32 },
        }

        fn main() -> Maybe {
            Maybe::Just
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("struct enum variant path should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "path expression");
            assert!(
                detail.contains("Maybe::Just") && detail.contains("named fields"),
                "detail should explain the missing named fields, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_rejects_unknown_qself_path_expression() {
    let source = r#"
        enum Flag {
            Ready,
        }

        fn main() -> Flag {
            <Flag>::Missing
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("unknown qself path should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "path expression");
            assert!(
                detail.contains("known top-level enum variant")
                    && detail.contains("known associated constant"),
                "detail should explain the unsupported qself path, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_rejects_struct_qself_path_expression() {
    let source = r#"
        enum Maybe {
            Just { value: u32 },
        }

        fn main() -> Maybe {
            <Maybe>::Just
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("struct qself path should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "path expression");
            assert!(detail.contains("named fields"));
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}
