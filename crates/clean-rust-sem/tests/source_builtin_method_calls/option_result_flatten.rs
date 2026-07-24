// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::expr::EvalResult;
use clean_rust_sem::{SourceProgram, Value};

fn run_source(source: &str, parse_msg: &str) -> EvalResult {
    let program = SourceProgram::parse(source).expect(parse_msg);
    let mut interp = Interpreter::new();
    program.run(&mut interp)
}

#[test]
fn test_option_flatten_some_some_returns_inner_option() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<Option<u32>> = Option::Some(Option::Some(42u32));
            x.flatten().unwrap()
        }
    "#;
    let result = run_source(source, "Option::flatten(Some(Some)) should parse");
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_flatten_some_none_returns_none() {
    let source = r#"
        fn main() -> bool {
            let x: Option<Option<u32>> = Option::Some(Option::None);
            x.flatten().is_none()
        }
    "#;
    let result = run_source(source, "Option::flatten(Some(None)) should parse");
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_option_flatten_none_stays_none() {
    let source = r#"
        fn main() -> bool {
            let x: Option<Option<u32>> = Option::None;
            x.flatten().is_none()
        }
    "#;
    let result = run_source(source, "Option::flatten(None) should parse");
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_option_flatten_rejects_non_nested_option_payload() {
    let source = r#"
        fn main() -> Option<u32> {
            let x: Option<u32> = Option::Some(42u32);
            x.flatten()
        }
    "#;
    let result = run_source(source, "Option::flatten(non-nested) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "Option::flatten() requires nested Option payload")
    );
}

#[test]
fn test_option_flatten_rejects_arguments() {
    let source = r#"
        fn main() -> Option<u32> {
            let x: Option<Option<u32>> = Option::Some(Option::Some(1u32));
            x.flatten(Option::Some(2u32))
        }
    "#;
    let result = run_source(source, "Option::flatten(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `flatten` takes 0 args, got 1")
    );
}

#[test]
fn test_result_flatten_ok_ok_returns_inner_result() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<Result<u32, u32>, u32> = Result::Ok(Result::Ok(42u32));
            x.flatten().unwrap()
        }
    "#;
    let result = run_source(source, "Result::flatten(Ok(Ok)) should parse");
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_flatten_ok_err_returns_inner_error() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<Result<u32, u32>, u32> = Result::Ok(Result::Err(7u32));
            match x.flatten() {
                Result::Ok(_) => 0u32,
                Result::Err(err) => err,
            }
        }
    "#;
    let result = run_source(source, "Result::flatten(Ok(Err)) should parse");
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_result_flatten_err_stays_err() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<Result<u32, u32>, u32> = Result::Err(11u32);
            match x.flatten() {
                Result::Ok(_) => 0u32,
                Result::Err(err) => err,
            }
        }
    "#;
    let result = run_source(source, "Result::flatten(Err) should parse");
    assert_eq!(result.value(), Some(Value::u32(11)));
}

#[test]
fn test_result_flatten_rejects_non_nested_result_payload() {
    let source = r#"
        fn main() -> Result<u32, u32> {
            let x: Result<u32, u32> = Result::Ok(42u32);
            x.flatten()
        }
    "#;
    let result = run_source(source, "Result::flatten(non-nested) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "Result::flatten() requires nested Result payload")
    );
}

#[test]
fn test_result_flatten_rejects_arguments() {
    let source = r#"
        fn main() -> Result<u32, u32> {
            let x: Result<Result<u32, u32>, u32> = Result::Ok(Result::Ok(1u32));
            x.flatten(Result::Ok(2u32))
        }
    "#;
    let result = run_source(source, "Result::flatten(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `flatten` takes 0 args, got 1")
    );
}
