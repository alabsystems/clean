// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::expr::EvalResult;
use clean_rust_sem::SourceProgram;

fn run_source(source: &str, parse_msg: &str) -> EvalResult {
    let program = SourceProgram::parse(source).expect(parse_msg);
    let mut interp = Interpreter::new();
    program.run(&mut interp)
}

#[test]
fn test_option_unwrap_rejects_arguments() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(1u32);
            x.unwrap(2u32)
        }
    "#;
    let result = run_source(source, "Option::unwrap(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `unwrap` takes 0 args, got 1")
    );
}

#[test]
fn test_option_expect_rejects_no_arguments() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(1u32);
            x.expect()
        }
    "#;
    let result = run_source(source, "Option::expect() should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `expect` takes 1 arg, got 0")
    );
}

#[test]
fn test_option_is_some_rejects_arguments() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::Some(1u32);
            x.is_some(2u32)
        }
    "#;
    let result = run_source(source, "Option::is_some(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `is_some` takes 0 args, got 1")
    );
}

#[test]
fn test_option_is_none_rejects_arguments() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::None;
            x.is_none(2u32)
        }
    "#;
    let result = run_source(source, "Option::is_none(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `is_none` takes 0 args, got 1")
    );
}

#[test]
fn test_result_unwrap_rejects_arguments() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.unwrap(2u32)
        }
    "#;
    let result = run_source(source, "Result::unwrap(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `unwrap` takes 0 args, got 1")
    );
}

#[test]
fn test_result_is_ok_rejects_arguments() {
    let source = r#"
        fn main() -> bool {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.is_ok(2u32)
        }
    "#;
    let result = run_source(source, "Result::is_ok(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `is_ok` takes 0 args, got 1")
    );
}

#[test]
fn test_result_is_err_rejects_arguments() {
    let source = r#"
        fn main() -> bool {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.is_err(2u32)
        }
    "#;
    let result = run_source(source, "Result::is_err(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `is_err` takes 0 args, got 1")
    );
}

#[test]
fn test_result_ok_rejects_arguments() {
    let source = r#"
        fn main() -> Option<u32> {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.ok(2u32)
        }
    "#;
    let result = run_source(source, "Result::ok(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `ok` takes 0 args, got 1")
    );
}

#[test]
fn test_result_err_rejects_arguments() {
    let source = r#"
        fn main() -> Option<u32> {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.err(2u32)
        }
    "#;
    let result = run_source(source, "Result::err(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `err` takes 0 args, got 1")
    );
}
