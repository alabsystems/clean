// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

// --- Result::unwrap ---

#[test]
fn test_result_unwrap_ok_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(42u32);
            x.unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_unwrap_err_panics() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap() on Err should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(matches!(
        result,
        clean_rust_sem::expr::EvalResult::Panic(ref msg)
            if msg.contains("Result::unwrap()")
    ));
}

// --- Result::unwrap_err ---

#[test]
fn test_result_unwrap_err_on_err_returns_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(42u32);
            x.unwrap_err()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap_err(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_unwrap_err_on_ok_panics() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(42u32);
            x.unwrap_err()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap_err(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(matches!(
        result,
        clean_rust_sem::expr::EvalResult::Panic(ref msg)
            if msg.contains("Result::unwrap_err()")
    ));
}

#[test]
fn test_result_unwrap_err_rejects_arguments() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(42u32);
            x.unwrap_err(1u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap_err(args) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `unwrap_err` takes 0 args, got 1")
    );
}

// --- Result::is_ok / Result::is_err ---

#[test]
fn test_result_is_ok_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.is_ok()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::is_ok() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_result_is_err_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.is_err()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::is_err() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

// --- Result::map ---

#[test]
fn test_result_map_ok_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(41u32);
            x.map(|value| value + 1u32).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::map() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_map_err_preserves_error() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(7u32);
            match x.map(|value| value + 1u32) {
                Result::Ok(_) => 0u32,
                Result::Err(err) => err,
            }
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::map(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

// --- Result::expect / Result::expect_err ---

#[test]
fn test_result_expect_ok_returns_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(42u32);
            x.expect("should not fail")
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::expect(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_expect_err_panics_with_message() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.expect("operation failed")
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::expect(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(matches!(
        result,
        clean_rust_sem::expr::EvalResult::Panic(ref msg)
            if msg == "operation failed"
    ));
}

#[test]
fn test_result_expect_err_on_err_returns_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(42u32);
            x.expect_err("should fail")
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::expect_err(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_expect_err_on_ok_panics_with_message() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.expect_err("expected failure")
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::expect_err(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(matches!(
        result,
        clean_rust_sem::expr::EvalResult::Panic(ref msg)
            if msg == "expected failure"
    ));
}

#[test]
fn test_result_expect_err_rejects_no_arguments() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(42u32);
            x.expect_err()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::expect_err() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `expect_err` takes 1 arg, got 0")
    );
}

// --- Result::ok / Result::err ---

#[test]
fn test_result_ok_on_ok_returns_some() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(42u32);
            x.ok().unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::ok(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_ok_on_err_returns_none() {
    let source = r#"
        fn main() -> bool {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.ok().is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::ok(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_result_err_on_err_returns_some() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(42u32);
            x.err().unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::err(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_err_on_ok_returns_none() {
    let source = r#"
        fn main() -> bool {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.err().is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::err(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}
