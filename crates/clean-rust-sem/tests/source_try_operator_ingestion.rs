// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `?` operator desugaring in source ingestion.
//!
//! The `?` operator is desugared at parse time into a match expression
//! that handles both `Result<T, E>` and `Option<T>` without type inference.
//! `Option` and `Result` are pre-registered as built-in enums.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_try_operator_result_ok_propagates_value() {
    let source = r#"
        fn get_value(r: Result<u32, u32>) -> Result<u32, u32> {
            let v: u32 = r?;
            Result::Ok(v)
        }

        fn main() -> u32 {
            let ok: Result<u32, u32> = Result::Ok(10u32);
            match get_value(ok) {
                Result::Ok(v) => v,
                Result::Err(_e) => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(10)));
}

#[test]
fn test_try_operator_result_err_early_returns() {
    let source = r#"
        fn get_value(r: Result<u32, u32>) -> Result<u32, u32> {
            let v: u32 = r?;
            Result::Ok(v)
        }

        fn main() -> u32 {
            let err: Result<u32, u32> = Result::Err(99u32);
            match get_value(err) {
                Result::Ok(_v) => 0u32,
                Result::Err(e) => e,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(99)));
}

#[test]
fn test_try_operator_option_some_propagates_value() {
    let source = r#"
        fn extract(opt: Option<u32>) -> Option<u32> {
            let v: u32 = opt?;
            Option::Some(v)
        }

        fn main() -> u32 {
            let some: Option<u32> = Option::Some(7u32);
            match extract(some) {
                Option::Some(v) => v,
                Option::None => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_try_operator_option_none_early_returns() {
    let source = r#"
        fn extract(opt: Option<u32>) -> Option<u32> {
            let v: u32 = opt?;
            Option::Some(v)
        }

        fn main() -> u32 {
            let none: Option<u32> = Option::None;
            match extract(none) {
                Option::Some(_v) => 1u32,
                Option::None => 42u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_try_operator_chained_result() {
    let source = r#"
        fn step1(x: u32) -> Result<u32, u32> {
            Result::Ok(x)
        }

        fn step2(x: u32) -> Result<u32, u32> {
            Result::Ok(x)
        }

        fn pipeline(x: u32) -> Result<u32, u32> {
            let a: u32 = step1(x)?;
            let b: u32 = step2(a)?;
            Result::Ok(b)
        }

        fn main() -> u32 {
            match pipeline(5u32) {
                Result::Ok(v) => v,
                Result::Err(_e) => 0u32,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(5)));
}

#[test]
fn test_try_operator_chained_result_short_circuits_on_first_error() {
    let source = r#"
        fn fail(_x: u32) -> Result<u32, u32> {
            Result::Err(77u32)
        }

        fn succeed(x: u32) -> Result<u32, u32> {
            Result::Ok(x)
        }

        fn pipeline(x: u32) -> Result<u32, u32> {
            let a: u32 = fail(x)?;
            let b: u32 = succeed(a)?;
            Result::Ok(b)
        }

        fn main() -> u32 {
            match pipeline(5u32) {
                Result::Ok(_v) => 0u32,
                Result::Err(e) => e,
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(77)));
}
