// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_runs_top_level_const_item() {
    let source = r#"
        const ANSWER: u32 = 42u32;

        fn main() -> u32 {
            ANSWER
        }
    "#;

    let program = SourceProgram::parse(source).expect("top-level const item should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_const_in_arithmetic() {
    let source = r#"
        const BASE: u32 = 40u32;

        fn add_two(x: u32) -> u32 {
            x + 2u32
        }

        fn main() -> u32 {
            add_two(BASE)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("const used in function argument should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_multiple_const_items() {
    let source = r#"
        const A: u32 = 10u32;
        const B: u32 = 20u32;
        const C: u32 = 12u32;

        fn main() -> u32 {
            A + B + C
        }
    "#;

    let program = SourceProgram::parse(source).expect("multiple const items should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_bool_const_item() {
    let source = r#"
        const IS_ENABLED: bool = true;

        fn main() -> bool {
            IS_ENABLED
        }
    "#;

    let program = SourceProgram::parse(source).expect("bool const item should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_program_runs_const_in_condition() {
    let source = r#"
        const THRESHOLD: u32 = 50u32;

        fn main() -> u32 {
            let x: u32 = 100u32;
            if x > THRESHOLD {
                42u32
            } else {
                0u32
            }
        }
    "#;

    let program = SourceProgram::parse(source).expect("const in condition should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_static_item() {
    let source = r#"
        static COUNTER: u32 = 42u32;

        fn main() -> u32 {
            COUNTER
        }
    "#;

    let program = SourceProgram::parse(source).expect("static item should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_static_mut_item() {
    let source = r#"
        static mut GLOBAL: u32 = 42u32;

        fn main() -> u32 {
            GLOBAL
        }
    "#;

    let program = SourceProgram::parse(source).expect("static mut item should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_const_with_struct() {
    let source = r#"
        struct Point {
            x: u32,
            y: u32,
        }

        const ORIGIN_X: u32 = 0u32;
        const ORIGIN_Y: u32 = 0u32;

        fn main() -> u32 {
            let p = Point { x: ORIGIN_X, y: ORIGIN_Y };
            p.x + p.y + 42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("const used in struct constructor should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_parses_const_item_ast() {
    let source = r#"
        const VALUE: u32 = 99u32;

        fn main() -> u32 {
            0u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("const item AST should parse");
    let const_item = program.items().iter().find(
        |item| matches!(item, clean_rust_sem::expr::Item::Const { name, .. } if name == "VALUE"),
    );
    assert!(
        const_item.is_some(),
        "const VALUE should appear in parsed items"
    );
}

#[test]
fn test_source_program_parses_static_item_ast() {
    let source = r#"
        static GLOBAL: u32 = 99u32;

        fn main() -> u32 {
            0u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("static item AST should parse");
    let static_item = program.items().iter().find(
        |item| matches!(item, clean_rust_sem::expr::Item::Static { name, .. } if name == "GLOBAL"),
    );
    assert!(
        static_item.is_some(),
        "static GLOBAL should appear in parsed items"
    );
}

#[test]
fn test_source_program_const_shadowed_by_local_let() {
    let source = r#"
        const X: u32 = 10u32;

        fn main() -> u32 {
            let X: u32 = 42u32;
            X
        }
    "#;

    let program = SourceProgram::parse(source).expect("const shadowed by local let should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_top_level_const_forward_references() {
    let source = r#"
        const ANSWER: u32 = BASE + OFFSET;
        const BASE: u32 = 40u32;
        const OFFSET: u32 = 2u32;

        fn main() -> u32 {
            ANSWER
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("forward-referenced top-level consts should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_block_const_forward_references() {
    let source = r#"
        fn main() -> u32 {
            let answer: u32 = ANSWER;
            const ANSWER: u32 = BASE + OFFSET;
            const BASE: u32 = 40u32;
            const OFFSET: u32 = 2u32;
            answer
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("forward-referenced block consts should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_runs_block_static_with_forward_const_initializer() {
    let source = r#"
        fn main() -> u32 {
            let answer: u32 = VALUE;
            static VALUE: u32 = BASE + OFFSET;
            const BASE: u32 = 40u32;
            const OFFSET: u32 = 2u32;
            answer
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("block static with forward const initializer should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
