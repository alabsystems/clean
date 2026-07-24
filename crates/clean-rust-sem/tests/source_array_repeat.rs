// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for array repeat expressions (`[expr; count]`) in source-ingested programs.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_source_array_repeat_basic() {
    let source = r#"
        fn main() -> u32 {
            let arr = [5u32; 3];
            arr[0] + arr[1] + arr[2]
        }
    "#;

    let program = SourceProgram::parse(source).expect("array repeat should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(15)));
}

#[test]
fn test_source_array_repeat_zero_value() {
    let source = r#"
        fn main() -> u32 {
            let arr = [0u32; 4];
            let mut sum = 0u32;
            for val in arr {
                sum += val;
            }
            sum
        }
    "#;

    let program = SourceProgram::parse(source).expect("zero-init array repeat should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(0)));
}

#[test]
fn test_source_array_repeat_mutation() {
    let source = r#"
        fn main() -> u32 {
            let mut arr = [1u32; 3];
            arr[1] = 42u32;
            arr[0] + arr[1] + arr[2]
        }
    "#;

    let program = SourceProgram::parse(source).expect("array repeat + mutation should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    // 1 + 42 + 1 = 44
    assert_eq!(result.value(), Some(Value::u32(44)));
}
