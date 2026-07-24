// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};

#[test]
fn test_source_program_alloc_qualified_format_macro() {
    let source = r#"
        fn main() -> bool {
            let s = alloc::format!("hello {}", 42u32);
            s == "hello 42"
        }
    "#;

    let program = SourceProgram::parse(source).expect("alloc::format!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_format_macro_supports_debug_and_escaped_braces() {
    let source = r#"
        fn main() -> bool {
            let label = "clean";
            let s = format!("{{{}}} {:?}", 42u32, label);
            s == "{42} \"clean\""
        }
    "#;

    let program = SourceProgram::parse(source).expect("format!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_format_macro_rejects_unsupported_specifiers() {
    let source = r#"
        fn main() {
            let _ = format!("{:x}", 42u32);
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("hex formatting should fail closed");
    assert!(matches!(
        &err,
        SourceError::Unsupported {
            context: "format macro",
            ..
        }
    ));
    assert!(
        err.to_string().contains("unsupported format placeholder"),
        "unexpected error: {err}"
    );
}

#[test]
fn test_source_program_stringify_macro() {
    let source = r#"
        fn main() -> bool {
            let s = stringify!(hello world);
            s == "hello world"
        }
    "#;

    let program = SourceProgram::parse(source).expect("stringify!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_concat_macro_concatenates_literal_fragments() {
    let source = r#"
        fn main() -> bool {
            let s = concat!("clean", '-', 4u32, true, 'x');
            s == "clean-4u32truex"
        }
    "#;

    let program = SourceProgram::parse(source).expect("concat!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_concat_macro_supports_nested_stringify_and_negative_numbers() {
    let source = r#"
        fn main() -> bool {
            let s = concat!(stringify!(hello world), ":", -7i32, ",", 3.5f32);
            s == "hello world:-7i32,3.5f32"
        }
    "#;

    let program = SourceProgram::parse(source).expect("nested concat!() should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}
