// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

fn run_main(source: &str) -> Option<Value> {
    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    program.run(&mut interpreter).value()
}

#[test]
fn test_source_program_let_annotation_coerces_function_item_to_fn_pointer() {
    let source = r#"
        fn add_one(x: u32) -> u32 { x + 1u32 }

        fn main() -> u32 {
            let f: fn(u32) -> u32 = add_one;
            f(41u32)
        }
    "#;

    assert_eq!(run_main(source), Some(Value::u32(42)));
}

#[test]
fn test_source_program_return_coerces_function_item_to_fn_pointer() {
    let source = r#"
        fn add_one(x: u32) -> u32 { x + 1u32 }

        fn chooser() -> fn(u32) -> u32 {
            add_one
        }

        fn main() -> u32 {
            chooser()(41u32)
        }
    "#;

    assert_eq!(run_main(source), Some(Value::u32(42)));
}
