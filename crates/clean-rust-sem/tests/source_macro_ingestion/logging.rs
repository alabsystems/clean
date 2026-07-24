// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_logging_macros_are_noops() {
    let source = r#"
        fn main() -> u32 {
            trace!("entering function");
            debug!("debug value: {}", 42);
            info!("processing request");
            warn!("deprecated usage");
            error!("something went wrong");
            log!("generic log");
            100u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("logging macros should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(100)));
}

#[test]
fn test_source_program_qualified_logging_macros_are_noops() {
    let source = r#"
        fn main() -> u32 {
            log::info!("log crate info");
            log::error!("log crate error");
            tracing::debug!("tracing debug");
            tracing::warn!("tracing warn");
            200u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("qualified logging macros should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(200)));
}
