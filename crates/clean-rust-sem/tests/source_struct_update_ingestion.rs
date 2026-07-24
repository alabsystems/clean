// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for struct update syntax in source ingestion.

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_source_program_runs_struct_update_expression() {
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        fn main() -> u32 {
            let base = Point { x: 40u32, y: 1u32 };
            let point = Point { y: 2u32, ..base };
            point.x + point.y
        }
    "#;

    let program = SourceProgram::parse(source).expect("struct update syntax should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_type_alias_struct_literal_and_pattern() {
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        type PointAlias = Point;

        fn main() -> u32 {
            let point = PointAlias { x: 40u32, y: 2u32 };
            match point {
                Point { x, y } => x + y,
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("type-alias struct literal and pattern should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_type_alias_struct_update_expression() {
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        type PointAlias = Point;

        fn main() -> u32 {
            let base = Point { x: 40u32, y: 1u32 };
            let point = PointAlias { y: 2u32, ..base };
            point.x + point.y
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("type-alias struct update syntax should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_struct_update_preserves_field_before_base_order() {
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        fn main() -> u32 {
            let mut step: u32 = 0u32;
            let point = Point {
                x: {
                    step += 1u32;
                    step
                },
                ..{
                    let current = step;
                    step += 10u32;
                    Point { x: current, y: step }
                }
            };
            point.x + point.y
        }
    "#;

    let program = SourceProgram::parse(source).expect("struct update order test should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(12)));
}

#[test]
fn test_source_program_runs_qualified_path_struct_update() {
    // Rust allows `self::Foo { ..base }` — the parser resolves the last path
    // segment as the struct name in its flat namespace model.
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        fn main() -> u32 {
            let base = Point { x: 40u32, y: 1u32 };
            let point = self::Point { y: 2u32, ..base };
            point.x + point.y
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("qualified-path struct update syntax should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_block_local_struct_update() {
    let source = r#"
        fn main() -> u32 {
            struct Point {
                x: u32,
                y: u32,
            }

            let base = Point { x: 40u32, y: 1u32 };
            let point = Point { y: 2u32, ..base };
            point.x + point.y
        }
    "#;

    let program = SourceProgram::parse(source).expect("block-local struct update should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
