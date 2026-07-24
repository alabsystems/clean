// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::eval::Interpreter;
use clean_rust_sem::types::{ReceiverMode, RustType, UintType};
use clean_rust_sem::{SourceError, SourceProgram, Value};

#[test]
fn test_qualified_associated_function_call_runs() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }

        fn main() -> u32 {
            let counter = Counter::new();
            counter.value
        }
    "#;

    let program = SourceProgram::parse(source).expect("associated function syntax should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_qualified_associated_function_call_ignores_same_named_free_function() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }

        fn new() -> Counter {
            Counter { value: 7u32 }
        }

        fn main() -> u32 {
            let counter = Counter::new();
            counter.value
        }
    "#;

    let program = SourceProgram::parse(source).expect("qualified associated function should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_type_alias_associated_function_call_uses_underlying_impl() {
    let source = r#"
        fn main() -> u32 {
            let counter = CounterAlias::new();
            counter.value
        }

        type CounterAlias = Counter;

        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("type alias associated function should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_qself_associated_function_call_runs() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }

        fn main() -> u32 {
            let counter = <Counter>::new();
            counter.value
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("qself associated function syntax should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_qself_type_alias_associated_function_call_uses_underlying_impl() {
    let source = r#"
        fn main() -> u32 {
            let counter = <CounterAlias>::new();
            counter.value
        }

        type CounterAlias = Counter;

        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("qself alias associated function should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_self_associated_function_call_runs_in_inherent_impl() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }

            fn load() -> u32 {
                let counter = Self::new();
                counter.value
            }
        }

        fn main() -> u32 {
            Counter::load()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("Self::new() should parse in an inherent impl");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_associated_function_path_value_runs() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }

        fn main() -> u32 {
            let ctor = Counter::new;
            let counter = ctor();
            counter.value
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("associated function path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_qself_type_alias_associated_function_path_value_uses_underlying_impl() {
    let source = r#"
        fn main() -> u32 {
            let ctor = <CounterAlias>::new;
            let counter = ctor();
            counter.value
        }

        type CounterAlias = Counter;

        struct Counter {
            value: u32,
        }

        impl Counter {
            fn new() -> Counter {
                Counter { value: 42u32 }
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("qself alias associated function path should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_inherent_ufcs_borrowed_receiver_path_value_runs() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn peek(&self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let peek = Counter::peek;
            let counter = Counter { value: 42u32 };
            peek(&counter)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("UFCS borrowed receiver path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_inherent_ufcs_borrowed_receiver_call_runs() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn peek(&self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let counter = Counter { value: 42u32 };
            Counter::peek(&counter)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("inherent UFCS borrowed receiver should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_associated_function_call_runs() {
    let source = r#"
        trait Factory {
            fn seed(self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {
            fn seed(self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let counter = Counter { value: 42u32 };
            <Counter as Factory>::seed(counter)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait-qualified associated functions should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_associated_function_call_with_borrowed_receiver_runs() {
    let source = r#"
        trait Factory {
            fn seed(&self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {
            fn seed(&self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let counter = Counter { value: 42u32 };
            <Counter as Factory>::seed(&counter)
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified borrowed receiver associated function should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_static_associated_function_call_runs() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;
        }

        struct Counter;

        impl Factory for Counter {
            fn seed() -> u32 {
                42u32
            }
        }

        fn main() -> u32 {
            <Counter as Factory>::seed()
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified static associated functions should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_static_trait_associated_function_registers_static_receiver_metadata() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("static trait associated functions should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
    let trait_def = interpreter
        .ctx
        .get_trait_def("Factory")
        .expect("trait definition should be registered");
    assert_eq!(trait_def.methods.len(), 1);
    assert_eq!(trait_def.methods[0].name, "seed");
    assert_eq!(trait_def.methods[0].receiver, ReceiverMode::Static);
    assert!(trait_def.methods[0].params.is_empty());
    assert_eq!(trait_def.methods[0].ret, RustType::Uint(UintType::U32));
}

#[test]
fn test_trait_qualified_type_alias_associated_function_call_uses_underlying_impl() {
    let source = r#"
        trait Factory {
            fn seed(self) -> u32;
        }

        fn main() -> u32 {
            let counter = Counter { value: 42u32 };
            <CounterAlias as Factory>::seed(counter)
        }

        type CounterAlias = Counter;

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {
            fn seed(self) -> u32 {
                self.value
            }
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified alias associated functions should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_static_associated_function_type_alias_uses_underlying_impl() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;
        }

        fn main() -> u32 {
            <CounterAlias as Factory>::seed()
        }

        type CounterAlias = Counter;

        struct Counter;

        impl Factory for Counter {
            fn seed() -> u32 {
                42u32
            }
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified alias static associated functions should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_default_method_call_runs() {
    let source = r#"
        trait Factory {
            fn seed(self) -> u32 {
                42u32
            }
        }

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {}

        fn main() -> u32 {
            let counter = Counter { value: 7u32 };
            <Counter as Factory>::seed(counter)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait-qualified default method should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_static_default_method_call_runs() {
    let source = r#"
        trait Factory {
            fn seed() -> u32 {
                42u32
            }
        }

        struct Counter;

        impl Factory for Counter {}

        fn main() -> u32 {
            <Counter as Factory>::seed()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait-qualified static default method should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_receiver_method_lookup_ignores_static_trait_associated_functions() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {
            fn seed() -> u32 {
                42u32
            }
        }

        fn main() -> u32 {
            let counter = Counter { value: 1u32 };
            counter.seed()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("receiver lookup regression should still parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    match result {
        clean_rust_sem::expr::EvalResult::Error(detail) => {
            assert!(
                detail.contains("undefined method `seed`"),
                "receiver syntax should not resolve static trait associated functions, got: {detail}"
            );
        }
        other => panic!("expected undefined-method error, got {other:?}"),
    }
}

#[test]
fn test_trait_qualified_associated_function_path_value_runs() {
    let source = r#"
        trait Factory {
            fn seed(self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {
            fn seed(self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let seed = <Counter as Factory>::seed;
            let counter = Counter { value: 42u32 };
            seed(counter)
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified associated function path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_type_alias_associated_function_path_value_uses_underlying_impl() {
    let source = r#"
        trait Factory {
            fn seed(self) -> u32;
        }

        fn main() -> u32 {
            let seed = <CounterAlias as Factory>::seed;
            let counter = Counter { value: 42u32 };
            seed(counter)
        }

        type CounterAlias = Counter;

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {
            fn seed(self) -> u32 {
                self.value
            }
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified alias associated function path should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_trait_qualified_default_method_path_value_runs() {
    let source = r#"
        trait Factory {
            fn seed(self) -> u32 {
                42u32
            }
        }

        struct Counter {
            value: u32,
        }

        impl Factory for Counter {}

        fn main() -> u32 {
            let seed = <Counter as Factory>::seed;
            let counter = Counter { value: 7u32 };
            seed(counter)
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified default-method path value should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_qself_associated_function_call_rejects_unknown_method() {
    let source = r#"
        struct Counter;

        fn main() -> u32 {
            <Counter>::missing()
        }
    "#;

    let err =
        SourceProgram::parse(source).expect_err("unknown qself associated function should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "call expression");
            assert!(
                detail.contains("<Counter>::missing")
                    && detail.contains("known associated function"),
                "detail should explain the unsupported qself associated function, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_trait_qualified_associated_function_call_rejects_unknown_method() {
    let source = r#"
        trait Factory {
            fn seed() -> u32;
        }

        struct Counter;

        impl Factory for Counter {
            fn seed() -> u32 {
                42u32
            }
        }

        fn main() -> u32 {
            <Counter as Factory>::missing()
        }
    "#;

    let err = SourceProgram::parse(source)
        .expect_err("unknown trait-qualified associated function should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "call expression");
            assert!(
                detail.contains("<Counter as Factory>::missing")
                    && detail.contains("known associated function"),
                "detail should explain the unsupported trait-qualified associated function, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_qualified_unit_enum_variant_call_rejects_parens() {
    let source = r#"
        enum Flag {
            Ready,
        }

        fn main() -> u32 {
            match Flag::Ready() {
                Flag::Ready => 42u32,
            }
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("unit enum variant call syntax should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "call expression");
            assert!(
                detail.contains("Flag::Ready") && detail.contains("unit enum variant"),
                "detail should explain the invalid unit enum variant call, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_qself_struct_enum_variant_call_rejects_positional_args() {
    let source = r#"
        enum Packet {
            Data { value: u32 },
        }

        fn main() -> u32 {
            match <Packet>::Data(42u32) {
                Packet::Data { value } => value,
            }
        }
    "#;

    let err = SourceProgram::parse(source)
        .expect_err("qself struct enum variant call syntax should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "call expression");
            assert!(
                detail.contains("struct enum variant") && detail.contains("named fields"),
                "detail should explain the invalid struct enum variant call, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

/// Regression: #2634 — borrowed `&mut self` receiver in trait-qualified call
/// preserves struct payload for field access.
#[test]
fn test_trait_qualified_mut_borrowed_receiver_preserves_field_access() {
    let source = r#"
        trait Stepper {
            fn step(&mut self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Stepper for Counter {
            fn step(&mut self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let mut counter = Counter { value: 7u32 };
            <Counter as Stepper>::step(&mut counter)
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("trait-qualified &mut self borrowed receiver should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(7)));
}

/// Regression: #2634 — borrowed receiver with multiple field accesses in
/// the same method body.
#[test]
fn test_borrowed_receiver_multiple_field_accesses() {
    let source = r#"
        trait Summarize {
            fn total(&self) -> u32;
        }

        struct Pair {
            a: u32,
            b: u32,
        }

        impl Summarize for Pair {
            fn total(&self) -> u32 {
                self.a + self.b
            }
        }

        fn main() -> u32 {
            let pair = Pair { a: 10u32, b: 32u32 };
            <Pair as Summarize>::total(&pair)
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("borrowed receiver with multi-field access should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

/// Regression: #2634 — inherent UFCS borrowed &mut self receiver preserves
/// struct payload.
#[test]
fn test_inherent_ufcs_mut_borrowed_receiver_preserves_field_access() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        impl Counter {
            fn peek(&mut self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            let mut counter = Counter { value: 42u32 };
            Counter::peek(&mut counter)
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("inherent UFCS &mut self borrowed receiver should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
