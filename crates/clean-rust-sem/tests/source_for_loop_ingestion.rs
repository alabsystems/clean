// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `for` loop range support in source ingestion.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_source_program_runs_for_loop_over_exclusive_u32_range() {
    let source = r#"
        fn main() -> u32 {
            let mut total: u32 = 0u32;
            for value in 1u32..4u32 {
                total = total + value;
            }
            total
        }
    "#;

    let program = SourceProgram::parse(source).expect("exclusive range for loop should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(6)));
}

#[test]
fn test_source_program_runs_for_loop_over_inclusive_i32_range() {
    let source = r#"
        fn main() -> i32 {
            let mut total: i32 = 0i32;
            for value in -1i32..=1i32 {
                total = total + value;
            }
            total
        }
    "#;

    let program = SourceProgram::parse(source).expect("inclusive range for loop should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::i32(0)));
}
