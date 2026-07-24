// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceProgram, Value};

#[test]
fn test_source_program_runs_trait_method_with_self_param_and_return() {
    let source = r#"
        trait Merge {
            fn merge(self, other: Self) -> Self;
        }

        struct Counter {
            value: u32,
        }

        impl Merge for Counter {
            fn merge(self, other: Counter) -> Counter {
                Counter { value: self.value + other.value }
            }
        }

        fn main() -> u32 {
            let left = Counter { value: 40u32 };
            let right = Counter { value: 2u32 };
            left.merge(right).value
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait method with Self param/return should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

// --- Acceptance criteria for #2636: Self-to-concrete-type substitution ---

#[test]
fn test_trait_method_returning_self_evaluates_through_dispatch() {
    let source = r#"
        trait Cloneable {
            fn duplicate(&self) -> Self;
        }

        struct Point {
            x: i32,
            y: i32,
        }

        impl Cloneable for Point {
            fn duplicate(&self) -> Point {
                Point { x: self.x, y: self.y }
            }
        }

        fn main() -> i32 {
            let p = Point { x: 3i32, y: 4i32 };
            let q = p.duplicate();
            q.x + q.y
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait with Self return should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::i32(7)));
}

#[test]
fn test_trait_method_with_self_param_type_checks_through_dispatch() {
    let source = r#"
        trait Combinable {
            fn combine(&self, other: Self) -> i32;
        }

        struct Pair {
            a: i32,
            b: i32,
        }

        impl Combinable for Pair {
            fn combine(&self, other: Pair) -> i32 {
                self.a + self.b + other.a + other.b
            }
        }

        fn main() -> i32 {
            let p1 = Pair { a: 1i32, b: 2i32 };
            let p2 = Pair { a: 3i32, b: 4i32 };
            p1.combine(p2)
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait with Self param should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::i32(10)));
}

#[test]
fn test_trait_method_returning_option_self_evaluates_through_dispatch() {
    let source = r#"
        trait TryClone {
            fn try_clone(&self) -> Option<Self>;
        }

        struct Num {
            value: i32,
        }

        impl TryClone for Num {
            fn try_clone(&self) -> Option<Num> {
                Option::Some(Num { value: self.value })
            }
        }

        fn main() -> i32 {
            let n = Num { value: 42i32 };
            match n.try_clone() {
                Option::Some(c) => c.value,
                Option::None => 0i32,
            }
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait method returning Option<Self> should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::i32(42)));
}

/// Verifies that `&Self` in trait param signatures substitutes correctly to
/// `&ConcreteType` so that signature validation passes. The impl body uses
/// a by-value Self param to avoid the known reference-field-access bug (#2634).
#[test]
fn test_trait_method_with_self_param_substituted_through_dispatch() {
    let source = r#"
        trait Addable {
            fn add_to(&self, other: Self) -> i32;
        }

        struct Num {
            value: i32,
        }

        impl Addable for Num {
            fn add_to(&self, other: Num) -> i32 {
                self.value + other.value
            }
        }

        fn main() -> i32 {
            let n = Num { value: 40i32 };
            let m = Num { value: 2i32 };
            n.add_to(m)
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait method with Self param should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::i32(42)));
}

#[test]
fn test_default_method_body_self_types_substituted_for_concrete_type() {
    let source = r#"
        trait Summarizer {
            fn value(&self) -> u32;

            fn double_value(&self) -> u32 {
                self.value() + self.value()
            }
        }

        struct Amount {
            n: u32,
        }

        impl Summarizer for Amount {
            fn value(&self) -> u32 {
                self.n
            }
        }

        fn main() -> u32 {
            let a = Amount { n: 21u32 };
            a.double_value()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("default method with Self dispatch should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}
