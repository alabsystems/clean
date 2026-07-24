// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

// --- Option::unwrap / Option::expect / Option::is_some / Option::is_none / Option::map ---

#[test]
fn test_option_unwrap_some_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(42u32);
            x.unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::unwrap() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_unwrap_none_panics() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::unwrap() on None should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(matches!(
        result,
        clean_rust_sem::expr::EvalResult::Panic(ref msg)
            if msg.contains("Option::unwrap()")
    ));
}

#[test]
fn test_option_expect_some_parses_and_runs() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::Some(42u32);
            x.expect("should be present")
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::expect() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_expect_none_panics_with_message() {
    let source = r#"
        fn main() -> u32 {
            let x: Option<u32> = Option::None;
            x.expect("value was missing")
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::expect() on None should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert!(matches!(
        result,
        clean_rust_sem::expr::EvalResult::Panic(ref msg)
            if msg == "value was missing"
    ));
}

#[test]
fn test_option_is_some_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::Some(1u32);
            x.is_some()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::is_some() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_option_is_none_parses_and_runs() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::None;
            x.is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::is_none() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_option_map_some_parses_and_runs() {
    let source = r#"
        fn add_one(value: u32) -> u32 {
            value + 1u32
        }

        fn main() -> u32 {
            let x: Option<u32> = Option::Some(41u32);
            x.map(add_one).unwrap()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::map() should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_option_map_none_preserves_none() {
    let source = r#"
        fn main() -> bool {
            let x: Option<u32> = Option::None;
            x.map(|value| value + 1u32).is_none()
        }
    "#;
    let program = SourceProgram::parse(source).expect("Option::map(None) should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}
