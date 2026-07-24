// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

// --- Option::unwrap_or / Option::unwrap_or_else ---

#[test]
fn test_option_unwrap_or_none_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.unwrap_or(42u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::unwrap_or() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_unwrap_or_some_keeps_inner_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(7u32);
            x.unwrap_or(42u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::unwrap_or(Some) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_option_unwrap_or_else_none_uses_fallback() {
    let source = r#"
        fn fallback() -> u32 {
            42u32
        }

        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.unwrap_or_else(fallback)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::unwrap_or_else(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_unwrap_or_else_some_skips_fallback() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(7u32);
            x.unwrap_or_else(|| 42u32)
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::unwrap_or_else(Some) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

// --- Option::and_then ---

#[test]
fn test_option_and_then_some_chains() {
    let source = r#"
        fn double_if_even(x: u32) -> Option<u32> {
            if x % 2u32 == 0u32 {
                Option::Some(x * 2u32)
            } else {
                Option::None
            }
        }

        fn main() -> u32 {
            let x: Option<u32> = Option::Some(4u32);
            x.and_then(double_if_even).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::and_then(Some) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(8)));
}

#[test]
fn test_option_and_then_some_returns_none() {
    let source = r#"
        fn double_if_even(x: u32) -> Option<u32> {
            if x % 2u32 == 0u32 {
                Option::Some(x * 2u32)
            } else {
                Option::None
            }
        }

        fn main() -> bool {
            let x: Option<u32> = Option::Some(3u32);
            x.and_then(double_if_even).is_none()
        }
    "#;
    let program =
        SourceProgram::parse(source).expect("Option::and_then returning None should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_option_and_then_none_short_circuits() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::None;
            x.and_then(|v| Option::Some(v + 1u32)).is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::and_then(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

// --- Option::filter ---

#[test]
fn test_option_filter_keeps_matching() {
    let source = r#"
        fn is_even(x: u32) -> bool {
            x % 2u32 == 0u32
        }

        fn main() -> u32 {
            let x: Option<u32> = Option::Some(4u32);
            x.filter(is_even).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::filter(match) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(4)));
}

#[test]
fn test_option_filter_removes_non_matching() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::Some(3u32);
            x.filter(|v| v % 2u32 == 0u32).is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::filter(no match) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_option_filter_none_stays_none() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::None;
            x.filter(|_v| true).is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::filter(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

// --- Option::ok_or / Option::ok_or_else ---

#[test]
fn test_option_ok_or_some_returns_ok() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(42u32);
            x.ok_or(0u32).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::ok_or(Some) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_ok_or_none_returns_err() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::None;
            x.ok_or(99u32).is_err()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::ok_or(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_option_ok_or_else_none_calls_closure() {
    let source = r#"
        fn make_error() -> u32 {
            99u32
        }

        fn main() -> bool {
            let x: Option<u32> = Option::None;
            x.ok_or_else(make_error).is_err()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::ok_or_else(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

// --- Option::or / Option::or_else ---

#[test]
fn test_option_or_some_keeps_left_value() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(7u32);
            x.or(Option::Some(42u32)).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::or(Some) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_option_or_none_uses_rhs() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.or(Option::Some(42u32)).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::or(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_or_else_some_skips_closure() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(7u32);
            x.or_else(|| Option::Some(42u32)).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::or_else(Some) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(7)));
}

#[test]
fn test_option_or_else_none_calls_closure() {
    let source = r#"
        fn fallback() -> Option<u32> {
            Option::Some(42u32)
        }

        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.or_else(fallback).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::or_else(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_or_rejects_no_arguments() {
    let source = r#"
        fn main() -> Option<u32> {
            let x: Option<u32> = Option::Some(1u32);
            x.or()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::or() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `or` takes 1 arg, got 0")
    );
}

#[test]
fn test_option_or_else_rejects_no_arguments() {
    let source = r#"
        fn main() -> Option<u32> {
            let x: Option<u32> = Option::None;
            x.or_else()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::or_else() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(
        matches!(result, clean_rust_sem::expr::EvalResult::Error(ref msg) if msg == "method `or_else` takes 1 arg, got 0")
    );
}
