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
fn test_option_map_or_some_applies_mapper() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(20u32);
            x.map_or(1u32, |v| v * 2u32)
        }
    "#;
    let result = run_source(source, "Option::map_or(Some) should parse");
    assert_eq!(result.value(), Some(Value::u32(40)));
}

#[test]
fn test_option_map_or_none_returns_default() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.map_or(7u32, |v| v * 2u32)
        }
    "#;
    let result = run_source(source, "Option::map_or(None) should parse");
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_option_map_or_else_some_uses_mapper() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(20u32);
            x.map_or_else(|| 7u32, |v| v + 1u32)
        }
    "#;
    let result = run_source(source, "Option::map_or_else(Some) should parse");
    assert_eq!(result.value(), Some(Value::u32(21)));
}

#[test]
fn test_option_map_or_else_none_calls_default_closure() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.map_or_else(|| 7u32, |v| v + 1u32)
        }
    "#;
    let result = run_source(source, "Option::map_or_else(None) should parse");
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_option_map_or_rejects_one_argument() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(20u32);
            x.map_or(1u32)
        }
    "#;
    let result = run_source(source, "Option::map_or() should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `map_or` takes 2 args, got 1")
    );
}

#[test]
fn test_option_map_or_else_rejects_one_argument() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.map_or_else(|| 7u32)
        }
    "#;
    let result = run_source(source, "Option::map_or_else() should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `map_or_else` takes 2 args, got 1")
    );
}

#[test]
fn test_result_map_or_ok_applies_mapper() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(20u32);
            x.map_or(7u32, |v| v + 1u32)
        }
    "#;
    let result = run_source(source, "Result::map_or(Ok) should parse");
    assert_eq!(result.value(), Some(Value::u32(21)));
}

#[test]
fn test_result_map_or_err_returns_default() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(20u32);
            x.map_or(7u32, |v| v + 1u32)
        }
    "#;
    let result = run_source(source, "Result::map_or(Err) should parse");
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_result_map_or_else_ok_uses_mapper() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(20u32);
            x.map_or_else(|err| err + 100u32, |v| v * 2u32)
        }
    "#;
    let result = run_source(source, "Result::map_or_else(Ok) should parse");
    assert_eq!(result.value(), Some(Value::u32(40)));
}

#[test]
fn test_result_map_or_else_err_calls_error_mapper() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(20u32);
            x.map_or_else(|err| err + 1u32, |v| v * 2u32)
        }
    "#;
    let result = run_source(source, "Result::map_or_else(Err) should parse");
    assert_eq!(result.value(), Some(Value::u32(21)));
}

#[test]
fn test_result_map_or_rejects_one_argument() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(20u32);
            x.map_or(1u32)
        }
    "#;
    let result = run_source(source, "Result::map_or() should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `map_or` takes 2 args, got 1")
    );
}

#[test]
fn test_result_map_or_else_rejects_one_argument() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(20u32);
            x.map_or_else(|err| err + 1u32)
        }
    "#;
    let result = run_source(source, "Result::map_or_else() should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `map_or_else` takes 2 args, got 1")
    );
}
