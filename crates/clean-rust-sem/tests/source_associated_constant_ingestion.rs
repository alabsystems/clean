// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::{SourceProgram, Value};

#[test]
fn test_source_u32_max_resolves() {
    let source = r#"
        fn main() -> u32 {
            u32::MAX
        }
    "#;
    let program = SourceProgram::parse(source).expect("u32::MAX should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(u32::MAX)));
}

#[test]
fn test_source_qself_u32_max_resolves() {
    let source = r#"
        fn main() -> u32 {
            <u32>::MAX
        }
    "#;
    let program = SourceProgram::parse(source).expect("<u32>::MAX should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(u32::MAX)));
}

#[test]
fn test_source_qself_alias_u32_max_resolves() {
    let source = r#"
        type Count = u32;

        fn main() -> u32 {
            <Count>::MAX
        }
    "#;
    let program = SourceProgram::parse(source).expect("<Count>::MAX should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(u32::MAX)));
}

#[test]
fn test_source_u32_min_resolves() {
    let source = r#"
        fn main() -> u32 {
            u32::MIN
        }
    "#;
    let program = SourceProgram::parse(source).expect("u32::MIN should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(u32::MIN)));
}

#[test]
fn test_source_i32_min_max_in_comparison() {
    let source = r#"
        fn main() -> bool {
            let lo: i32 = i32::MIN;
            let hi: i32 = i32::MAX;
            lo < hi
        }
    "#;
    let program = SourceProgram::parse(source).expect("i32::MIN/MAX should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_u8_max_in_arithmetic() {
    let source = r#"
        fn main() -> u32 {
            let max: u8 = u8::MAX;
            max as u32
        }
    "#;
    let program = SourceProgram::parse(source).expect("u8::MAX in arithmetic should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(255)));
}

#[test]
fn test_source_u64_max_resolves() {
    let source = r#"
        fn main() -> u64 {
            u64::MAX
        }
    "#;
    let program = SourceProgram::parse(source).expect("u64::MAX should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u64(u64::MAX)));
}

#[test]
fn test_source_f64_infinity_resolves() {
    let source = r#"
        fn main() -> f64 {
            f64::INFINITY
        }
    "#;
    let program = SourceProgram::parse(source).expect("f64::INFINITY should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::f64(f64::INFINITY)));
}

#[test]
fn test_source_f64_constants_comparison() {
    let source = r#"
        fn main() -> bool {
            let min: f64 = f64::MIN;
            let max: f64 = f64::MAX;
            min < max
        }
    "#;
    let program = SourceProgram::parse(source).expect("f64 MIN/MAX should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::Bool(true)));
}

#[test]
fn test_source_associated_constant_in_match() {
    let source = r#"
        fn main() -> u32 {
            let x: u32 = 42u32;
            if x < u32::MAX {
                1u32
            } else {
                0u32
            }
        }
    "#;
    let program =
        SourceProgram::parse(source).expect("associated constant in condition should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(1)));
}

#[test]
fn test_source_inherent_associated_constant_resolves() {
    let source = r#"
        struct Counter;

        impl Counter {
            const BASE: u32 = 42u32;
        }

        fn main() -> u32 {
            Counter::BASE
        }
    "#;

    let program = SourceProgram::parse(source).expect("Counter::BASE should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_self_associated_constant_resolves_in_inherent_impl() {
    let source = r#"
        struct Counter;

        impl Counter {
            const BASE: u32 = 42u32;

            fn load() -> u32 {
                Self::BASE
            }
        }

        fn main() -> u32 {
            Counter::load()
        }
    "#;

    let program = SourceProgram::parse(source).expect("Self::BASE should parse in inherent impl");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_qself_alias_inherent_associated_constant_resolves() {
    let source = r#"
        type CounterAlias = Counter;

        struct Counter;

        impl Counter {
            const BASE: u32 = 42u32;
        }

        fn main() -> u32 {
            <CounterAlias>::BASE
        }
    "#;

    let program = SourceProgram::parse(source).expect("<CounterAlias>::BASE should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_top_level_const_can_reference_inherent_associated_constant() {
    let source = r#"
        struct Counter;

        impl Counter {
            const BASE: u32 = 40u32;
        }

        const ANSWER: u32 = Counter::BASE + 2u32;

        fn main() -> u32 {
            ANSWER
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("top-level const using inherent associated const should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_trait_qualified_associated_constant_path_resolves() {
    let source = r#"
        trait Bounded {
            const MAX: u32;
        }

        struct Counter;

        impl Bounded for Counter {
            const MAX: u32 = 42u32;
        }

        fn main() -> u32 {
            <Counter as Bounded>::MAX
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait-qualified associated constant should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_trait_default_method_self_associated_constant_path_resolves() {
    let source = r#"
        trait Bounded {
            const MAX: u32;

            fn load() -> u32 {
                Self::MAX
            }
        }

        struct Counter;

        impl Bounded for Counter {
            const MAX: u32 = 42u32;
        }

        fn main() -> u32 {
            <Counter as Bounded>::load()
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait default Self::MAX path should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_trait_impl_method_self_associated_constant_path_resolves() {
    let source = r#"
        trait Bounded {
            const MAX: u32;
            fn load() -> u32;
        }

        struct Counter;

        impl Bounded for Counter {
            const MAX: u32 = 42u32;

            fn load() -> u32 {
                Self::MAX
            }
        }

        fn main() -> u32 {
            <Counter as Bounded>::load()
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait impl Self::MAX path should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
