// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::expr::EvalResult;
use clean_rust_sem::types::Mutability;
use clean_rust_sem::values::EnumPayload;
use clean_rust_sem::{SourceProgram, Value};

fn run_source(source: &str, parse_msg: &str) -> EvalResult {
    let program = SourceProgram::parse(source).expect(parse_msg);
    let mut interp = Interpreter::new();
    program.run(&mut interp)
}

fn expect_option_reference(
    result: EvalResult,
    expected_mutability: Mutability,
    expected_value: Value,
) {
    let value = result.value().expect("program should return a value");
    match value {
        Value::Enum {
            name,
            variant,
            payload,
        } => {
            assert_eq!(name, "Option");
            assert_eq!(variant, "Some");
            match *payload {
                EnumPayload::Tuple(fields) if fields.len() == 1 => match &fields[0] {
                    Value::Reference {
                        mutability,
                        referent,
                        ..
                    } => {
                        assert_eq!(*mutability, expected_mutability);
                        assert_eq!(referent.as_deref(), Some(&expected_value));
                    }
                    other => panic!("expected Option reference payload, got {other:?}"),
                },
                other => panic!("expected single-field Option payload, got {other:?}"),
            }
        }
        other => panic!("expected Option return value, got {other:?}"),
    }
}

fn expect_result_reference(
    result: EvalResult,
    expected_variant: &str,
    expected_mutability: Mutability,
    expected_value: Value,
) {
    let value = result.value().expect("program should return a value");
    match value {
        Value::Enum {
            name,
            variant,
            payload,
        } => {
            assert_eq!(name, "Result");
            assert_eq!(variant, expected_variant);
            match *payload {
                EnumPayload::Tuple(fields) if fields.len() == 1 => match &fields[0] {
                    Value::Reference {
                        mutability,
                        referent,
                        ..
                    } => {
                        assert_eq!(*mutability, expected_mutability);
                        assert_eq!(referent.as_deref(), Some(&expected_value));
                    }
                    other => panic!("expected Result reference payload, got {other:?}"),
                },
                other => panic!("expected single-field Result payload, got {other:?}"),
            }
        }
        other => panic!("expected Result return value, got {other:?}"),
    }
}

#[test]
fn test_option_as_ref_some_returns_shared_reference() {
    let source = r#"
        fn main() -> Option<&u32> {
            let x: Option<u32> = Option::Some(42u32);
            x.as_ref()
        }
    "#;
    let result = run_source(source, "Option::as_ref(Some) should parse");
    expect_option_reference(result, Mutability::Shared, Value::u32(42));
}

#[test]
fn test_option_as_ref_none_stays_none() {
    let source = r#"
        fn main() -> Option<&u32> {
            let x: Option<u32> = Option::None;
            x.as_ref()
        }
    "#;
    let result = run_source(source, "Option::as_ref(None) should parse");
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_option_as_mut_some_returns_mutable_reference() {
    let source = r#"
        fn main() -> Option<&mut u32> {
            let mut x: Option<u32> = Option::Some(42u32);
            x.as_mut()
        }
    "#;
    let result = run_source(source, "Option::as_mut(Some) should parse");
    expect_option_reference(result, Mutability::Mutable, Value::u32(42));
}

#[test]
fn test_option_as_mut_none_stays_none() {
    let source = r#"
        fn main() -> Option<&mut u32> {
            let mut x: Option<u32> = Option::None;
            x.as_mut()
        }
    "#;
    let result = run_source(source, "Option::as_mut(None) should parse");
    assert_eq!(
        result.value(),
        Some(Value::Enum {
            name: "Option".to_string(),
            variant: "None".to_string(),
            payload: Box::new(EnumPayload::Unit),
        })
    );
}

#[test]
fn test_option_as_ref_rejects_arguments() {
    let source = r#"
        fn main() -> Option<&u32> {
            let x: Option<u32> = Option::Some(1u32);
            x.as_ref(2u32)
        }
    "#;
    let result = run_source(source, "Option::as_ref(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `as_ref` takes 0 args, got 1")
    );
}

#[test]
fn test_option_as_mut_rejects_arguments() {
    let source = r#"
        fn main() -> Option<&mut u32> {
            let mut x: Option<u32> = Option::Some(1u32);
            x.as_mut(2u32)
        }
    "#;
    let result = run_source(source, "Option::as_mut(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `as_mut` takes 0 args, got 1")
    );
}

#[test]
fn test_result_as_ref_ok_returns_shared_reference() {
    let source = r#"
        fn main() -> Result<&u32, u32> {
            let x: Result<u32, u32> = Result::Ok(42u32);
            x.as_ref()
        }
    "#;
    let result = run_source(source, "Result::as_ref(Ok) should parse");
    expect_result_reference(result, "Ok", Mutability::Shared, Value::u32(42));
}

#[test]
fn test_result_as_ref_err_returns_shared_reference() {
    let source = r#"
        fn main() -> Result<u32, &u32> {
            let x: Result<u32, u32> = Result::Err(7u32);
            x.as_ref()
        }
    "#;
    let result = run_source(source, "Result::as_ref(Err) should parse");
    expect_result_reference(result, "Err", Mutability::Shared, Value::u32(7));
}

#[test]
fn test_result_as_mut_ok_returns_mutable_reference() {
    let source = r#"
        fn main() -> Result<&mut u32, u32> {
            let mut x: Result<u32, u32> = Result::Ok(42u32);
            x.as_mut()
        }
    "#;
    let result = run_source(source, "Result::as_mut(Ok) should parse");
    expect_result_reference(result, "Ok", Mutability::Mutable, Value::u32(42));
}

#[test]
fn test_result_as_mut_err_returns_mutable_reference() {
    let source = r#"
        fn main() -> Result<u32, &mut u32> {
            let mut x: Result<u32, u32> = Result::Err(7u32);
            x.as_mut()
        }
    "#;
    let result = run_source(source, "Result::as_mut(Err) should parse");
    expect_result_reference(result, "Err", Mutability::Mutable, Value::u32(7));
}

#[test]
fn test_result_as_ref_rejects_arguments() {
    let source = r#"
        fn main() -> Result<&u32, u32> {
            let x: Result<u32, u32> = Result::Ok(1u32);
            x.as_ref(2u32)
        }
    "#;
    let result = run_source(source, "Result::as_ref(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `as_ref` takes 0 args, got 1")
    );
}

#[test]
fn test_result_as_mut_rejects_arguments() {
    let source = r#"
        fn main() -> Result<&mut u32, u32> {
            let mut x: Result<u32, u32> = Result::Ok(1u32);
            x.as_mut(2u32)
        }
    "#;
    let result = run_source(source, "Result::as_mut(args) should parse");
    assert!(
        matches!(result, EvalResult::Error(ref msg) if msg == "method `as_mut` takes 0 args, got 1")
    );
}
