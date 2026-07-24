// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::{eval::Interpreter, SourceProgram, Value};

fn run(source: &str) -> Value {
    let program = SourceProgram::parse(source).expect("source should parse");
    let mut interpreter = Interpreter::new();
    program
        .run(&mut interpreter)
        .value()
        .expect("program should return")
}

#[test]
fn evals_mov() {
    let source = r#"
        fn main() -> u32 {
            let mut dst = 1u32;
            let src = 7u32;
            unsafe {
                core::arch::asm!("mov {0:e}, {1:e}", lateout(reg) dst, in(reg) src, options(nomem));
            }
            dst
        }
    "#;
    assert_eq!(run(source), Value::u32(7));
}

#[test]
fn evals_add() {
    let source = r#"
        fn main() -> u32 {
            let mut dst = 10u32;
            let src = 5u32;
            unsafe {
                core::arch::asm!("add {0:e}, {1:e}", inout(reg) dst, in(reg) src, options(nomem));
            }
            dst
        }
    "#;
    assert_eq!(run(source), Value::u32(15));
}

#[test]
fn evals_sub() {
    let source = r#"
        fn main() -> u32 {
            let mut dst = 10u32;
            let src = 3u32;
            unsafe {
                core::arch::asm!("sub {0:e}, {1:e}", inout(reg) dst, in(reg) src, options(nomem));
            }
            dst
        }
    "#;
    assert_eq!(run(source), Value::u32(7));
}

#[test]
fn evals_xor() {
    let source = r#"
        fn main() -> u32 {
            let mut dst = 0b1010u32;
            let src = 0b1100u32;
            unsafe {
                core::arch::asm!("xor {0:e}, {1:e}", inout(reg) dst, in(reg) src, options(nomem));
            }
            dst
        }
    "#;
    assert_eq!(run(source), Value::u32(0b0110));
}
