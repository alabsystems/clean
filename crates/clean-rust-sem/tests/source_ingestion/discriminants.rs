// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_parses_c_like_enum_with_discriminants() {
    let source = r#"
        enum Color {
            Red = 1,
            Green = 2,
            Blue = 3,
        }

        fn main() -> u32 {
            let c = Color::Red;
            c as u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(1)));
}

#[test]
fn test_source_program_runs_enum_discriminant_auto_increment() {
    let source = r#"
        enum Status {
            Active = 10,
            Pending,
            Inactive,
        }

        fn main() -> u32 {
            let a = Status::Active as u32;
            let b = Status::Pending as u32;
            let c = Status::Inactive as u32;
            a + b + c
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    // 10 + 11 + 12 = 33
    assert_eq!(result.value(), Some(Value::u32(33)));
}

#[test]
fn test_source_program_runs_enum_discriminant_default_zero_start() {
    let source = r#"
        enum Priority {
            Low = 0,
            Medium = 1,
            High = 2,
        }

        fn main() -> u32 {
            Priority::High as u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(2)));
}

#[test]
fn test_source_program_runs_enum_discriminant_negative() {
    let source = r#"
        enum Offset {
            Behind = -1,
            Center = 0,
            Ahead = 1,
        }

        fn main() -> i32 {
            Offset::Behind as i32
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::i32(-1)));
}

#[test]
fn test_source_program_runs_enum_discriminant_cast_to_i64() {
    let source = r#"
        enum Size {
            Small = 100,
            Medium = 200,
            Large = 300,
        }

        fn main() -> i64 {
            Size::Large as i64
        }
    "#;

    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::i64(300)));
}
