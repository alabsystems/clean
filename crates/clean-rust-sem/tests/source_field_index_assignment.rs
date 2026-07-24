// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for field and index assignment in source-ingested programs.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_source_struct_field_assignment() {
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        fn main() -> u32 {
            let mut p = Point { x: 10u32, y: 20u32 };
            p.x = 32u32;
            p.x + p.y
        }
    "#;

    let program = SourceProgram::parse(source).expect("field assignment should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(52)));
}

#[test]
fn test_source_nested_struct_field_assignment() {
    let source = r#"
        struct Inner {
            value: u32,
        }

        struct Outer {
            inner: Inner,
            extra: u32,
        }

        fn main() -> u32 {
            let mut o = Outer {
                inner: Inner { value: 1u32 },
                extra: 40u32,
            };
            o.inner.value = 2u32;
            o.inner.value + o.extra
        }
    "#;

    let program = SourceProgram::parse(source).expect("nested field assignment should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_array_index_assignment() {
    let source = r#"
        fn main() -> u32 {
            let mut arr = [10u32, 20u32, 30u32];
            arr[1] = 32u32;
            arr[0] + arr[1]
        }
    "#;

    let program = SourceProgram::parse(source).expect("index assignment should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_compound_field_assignment() {
    let source = r#"
        struct Counter {
            count: u32,
        }

        fn main() -> u32 {
            let mut c = Counter { count: 40u32 };
            c.count += 2u32;
            c.count
        }
    "#;

    let program = SourceProgram::parse(source).expect("compound field assignment should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
