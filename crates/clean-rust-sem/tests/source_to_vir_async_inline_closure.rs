// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for inline async closure lowering and inference.

use clean_rust_sem::{LoweredProgram, RustType, SourceProgram, UintType};

fn lowered_program(source: &str) -> LoweredProgram {
    let program = SourceProgram::parse(source).expect("source should parse");
    program.lower_to_vir().expect("source should lower to VIR")
}

#[test]
fn test_inline_async_closure_call_await_infers_output() {
    let source = r#"
        fn main() -> u32 {
            let base = 1u32;
            let result = (async |x: u32| x + base)(4u32).await;
            result + result
        }
    "#;

    let lowered = lowered_program(source);
    let body = lowered
        .functions
        .get("main")
        .expect("lowered program should contain `main`");

    let result_local = body
        .locals
        .iter()
        .find(|local| local.name.as_deref() == Some("result"))
        .expect("lowered body should declare `result`");
    assert_eq!(
        result_local.ty,
        RustType::Uint(UintType::U32),
        "awaiting an inline async closure call should infer `u32`, got {:?}",
        result_local.ty
    );
}
