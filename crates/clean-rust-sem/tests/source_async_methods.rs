// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_async_inherent_method_parses_and_runs() {
    let source = r#"
        struct Counter {
            offset: u32,
        }

        impl Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + self.offset
            }
        }

        fn main() -> u32 {
            let counter = Counter { offset: 3u32 };
            let result = counter.compute(4u32).await;
            result + result
        }
    "#;

    let program = SourceProgram::parse(source).expect("async inherent method should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(14)));
}

#[test]
fn test_async_trait_method_parses_and_runs() {
    let source = r#"
        trait Worker {
            async fn compute(&self, x: u32) -> u32;
        }

        struct Counter {
            offset: u32,
        }

        impl Worker for Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + self.offset
            }
        }

        fn main() -> u32 {
            let counter = Counter { offset: 3u32 };
            let result = counter.compute(4u32).await;
            result + result
        }
    "#;

    let program = SourceProgram::parse(source).expect("async trait method should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(14)));
}

#[test]
fn test_async_inherent_method_path_value_parses_and_runs() {
    let source = r#"
        struct Counter {
            offset: u32,
        }

        impl Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + self.offset
            }
        }

        fn main() -> u32 {
            let counter = Counter { offset: 3u32 };
            let callee = Counter::compute;
            let result = callee(&counter, 4u32).await;
            result + result
        }
    "#;

    let program = SourceProgram::parse(source).expect("async inherent method path should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(14)));
}

#[test]
fn test_async_trait_method_path_value_parses_and_runs() {
    let source = r#"
        trait Worker {
            async fn compute(&self, x: u32) -> u32;
        }

        struct Counter {
            offset: u32,
        }

        impl Worker for Counter {
            async fn compute(&self, x: u32) -> u32 {
                x + self.offset
            }
        }

        fn main() -> u32 {
            let counter = Counter { offset: 3u32 };
            let callee = <Counter as Worker>::compute;
            let result = callee(&counter, 4u32).await;
            result + result
        }
    "#;

    let program = SourceProgram::parse(source).expect("async trait method path should parse");
    let mut interp = Interpreter::new();
    let result = program.run(&mut interp);
    assert_eq!(result.value(), Some(Value::u32(14)));
}
