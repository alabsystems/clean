// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Integration tests for built-in associated function ingestion.
//!
//! The source parser recognizes standard-library nominal types (`String`,
//! `Vec`, `Box`) so their associated-function call syntax (`String::new()`,
//! `Vec::with_capacity(10)`, etc.) parses and evaluates without requiring
//! a user-defined struct declaration.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_string_new_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::new();
            s == ""
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::new() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_string_new_path_value_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let make = String::new;
            let s = make();
            s == ""
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::new path value should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_string_from_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let s = String::from("hello");
            s == "hello"
        }
    "#;
    let program = SourceProgram::parse(source).expect("String::from() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_vec_new_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let v = Vec::new();
            let len: u32 = 0u32;
            len
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::new() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(0)));
}

#[test]
fn test_vec_with_capacity_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let v = Vec::with_capacity(16u32);
            let len: u32 = 0u32;
            len
        }
    "#;
    let program = SourceProgram::parse(source).expect("Vec::with_capacity() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(0)));
}

#[test]
fn test_box_new_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let b = Box::new(42u32);
            b
        }
    "#;
    let program = SourceProgram::parse(source).expect("Box::new() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_user_defined_string_new_shadows_builtin_intrinsic() {
    let source = r#"
        struct String {
            inner: u32,
        }

        impl String {
            fn new() -> String {
                String { inner: 99u32 }
            }
        }

        fn main() -> u32 {
            let s = String::new();
            s.inner
        }
    "#;
    let program = SourceProgram::parse(source).expect("shadowing String::new() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(99)));
}

#[test]
fn test_type_alias_vec_with_capacity_parses_and_runs() {
    let source = r#"
        type Numbers = Vec<u32>;

        fn main() -> bool {
            let values = Numbers::with_capacity(4u32);
            values.is_empty()
        }
    "#;
    let program =
        SourceProgram::parse(source).expect("type alias Vec::with_capacity() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_qself_type_alias_vec_with_capacity_parses_and_runs() {
    let source = r#"
        type Numbers = Vec<u32>;

        fn main() -> bool {
            let values = <Numbers>::with_capacity(4u32);
            values.is_empty()
        }
    "#;
    let program =
        SourceProgram::parse(source).expect("qself alias Vec::with_capacity() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_qself_vec_with_capacity_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let values = <Vec<u32>>::with_capacity(4u32);
            values.is_empty()
        }
    "#;
    let program = SourceProgram::parse(source).expect("qself Vec::with_capacity() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_string_new_parse_only() {
    // Verify parsing succeeds even if we don't execute
    let source = r#"
        fn main() {
            let _a = String::new();
            let _b = String::from("test");
            let _c = Vec::new();
            let _d = Vec::with_capacity(10u32);
            let _e = Box::new(true);
        }
    "#;
    SourceProgram::parse(source).expect("all builtin associated function calls should parse");
}
