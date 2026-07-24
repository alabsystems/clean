// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};

#[test]
fn test_source_program_runs_vec_macro() {
    let source = r#"
        fn main() -> u32 {
            let v = vec![10u32, 20u32, 12u32];
            v[0] + v[1] + v[2]
        }
    "#;

    let program = SourceProgram::parse(source).expect("vec![] should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_vec_repeat_macro() {
    let source = r#"
        fn main() -> u32 {
            let v = vec![14u32; 3usize];
            v[0] + v[1] + v[2]
        }
    "#;

    let program = SourceProgram::parse(source).expect("vec![value; count] should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_std_qualified_vec_macro() {
    let source = r#"
        fn main() -> u32 {
            let v = std::vec![10u32, 20u32, 12u32];
            v[0] + v[1] + v[2]
        }
    "#;

    let program = SourceProgram::parse(source).expect("std::vec![] should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_rejects_vec_repeat_macro_with_trailing_comma() {
    let source = r#"
        fn main() -> u32 {
            let _v = vec![14u32; 3usize,];
            42u32
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("vec![value; count,] should be rejected");

    match err {
        SourceError::Parse(err) => {
            assert!(
                err.to_string()
                    .contains("unexpected tokens after vec! repeat syntax"),
                "detail should explain the invalid repeat syntax, got: {err}"
            );
        }
        other => panic!("expected parse error, got {other:?}"),
    }
}
