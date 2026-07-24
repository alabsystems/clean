// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

// --- Result::unwrap_or / Result::unwrap_or_else ---

#[test]
fn test_result_unwrap_or_err_uses_fallback_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(7u32);
            x.unwrap_or(42u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap_or(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_unwrap_or_ok_keeps_inner_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(5u32);
            x.unwrap_or(42u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap_or(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(5)));
}

#[test]
fn test_result_unwrap_or_else_ok_skips_fallback() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(5u32);
            x.unwrap_or_else(|err| err + 10u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap_or_else(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(5)));
}

#[test]
fn test_result_unwrap_or_else_err_uses_fallback() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(32u32);
            x.unwrap_or_else(|err| err + 10u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::unwrap_or_else(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

// --- Result::and_then ---

#[test]
fn test_result_and_then_ok_chains() {
    let source = r#"
        fn checked_double(x: u32) -> Result<u32, u32> {
            if x < 100u32 {
                Result::Ok(x * 2u32)
            } else {
                Result::Err(x)
            }
        }

        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(21u32);
            x.and_then(checked_double).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::and_then(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_and_then_err_short_circuits() {
    let source = r#"
        fn main() -> bool {
            let x: Result<u32, u32> = Result::Err(7u32);
            x.and_then(|v| Result::Ok(v + 1u32)).is_err()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::and_then(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

// --- Result::map_err ---

#[test]
fn test_result_map_err_on_err_transforms() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(7u32);
            match x.map_err(|e| e * 3u32) {
                Result::Ok(_) => 0u32,
                Result::Err(e) => e,
            }
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::map_err(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(21)));
}

#[test]
fn test_result_map_err_on_ok_passes_through() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(42u32);
            x.map_err(|e| e * 3u32).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::map_err(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

// --- Result::or / Result::or_else ---

#[test]
fn test_result_or_ok_keeps_left_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(7u32);
            x.or(Result::Ok(42u32)).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::or(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_result_or_err_uses_rhs() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.or(Result::Ok(42u32)).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::or(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_or_else_ok_skips_closure() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Ok(7u32);
            x.or_else(|e| Result::Ok(e + 1u32)).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::or_else(Ok) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_result_or_else_err_calls_closure() {
    let source = r#"
        fn main() -> u32 {
            let x: Result<u32, u32> = Result::Err(41u32);
            x.or_else(|e| Result::Ok(e + 1u32)).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::or_else(Err) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_result_or_rejects_no_arguments() {
    let source = r#"
        fn main() -> Result<u32, u32> {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.or()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::or() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `or` takes 1 arg, got 0")
    );
}

#[test]
fn test_result_or_else_rejects_no_arguments() {
    let source = r#"
        fn main() -> Result<u32, u32> {
            let x: Result<u32, u32> = Result::Err(1u32);
            x.or_else()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Result::or_else() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `or_else` takes 1 arg, got 0")
    );
}
