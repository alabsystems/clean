// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};
use clean_rust_sem::expr::Item;

#[test]
fn test_source_program_uses_default_trait_method_body() {
    let source = r#"
        trait Adder {
            fn add(self, x: u32) -> u32 {
                x + 10u32
            }
        }

        struct Counter {
            value: u32,
        }

        impl Adder for Counter {}

        fn main() -> u32 {
            let c = Counter { value: 5u32 };
            c.add(32u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait with default method should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_overrides_default_trait_method_body() {
    let source = r#"
        trait Adder {
            fn add(self, x: u32) -> u32 {
                x + 10u32
            }
        }

        struct Counter {
            value: u32,
        }

        impl Adder for Counter {
            fn add(self, x: u32) -> u32 {
                self.value + x
            }
        }

        fn main() -> u32 {
            let c = Counter { value: 10u32 };
            c.add(32u32)
        }
    "#;

    let program = SourceProgram::parse(source).expect("overridden default method should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_default_method_with_self_field_access() {
    let source = r#"
        trait Doubler {
            fn double(self) -> u32 {
                self.value + self.value
            }
        }

        struct Num {
            value: u32,
        }

        impl Doubler for Num {}

        fn main() -> u32 {
            let n = Num { value: 21u32 };
            n.double()
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("default method with self access should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_trait_with_mixed_default_and_required_methods() {
    let source = r#"
        trait Ops {
            fn required(self) -> u32;
            fn default_op(self, x: u32) -> u32 {
                x + 2u32
            }
        }

        struct Widget {
            v: u32,
        }

        impl Ops for Widget {
            fn required(self) -> u32 {
                self.v
            }
        }

        fn main() -> u32 {
            let w = Widget { v: 10u32 };
            let r = w.required();
            let w2 = Widget { v: 0u32 };
            let d = w2.default_op(30u32);
            r + d
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("mixed default and required methods should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_supertrait_basic() {
    let source = r#"
        trait Base {
            fn base_val(&self) -> u32;
        }

        trait Sub: Base {
            fn sub_val(&self) -> u32;
        }

        struct Widget {
            x: u32,
        }

        impl Base for Widget {
            fn base_val(&self) -> u32 {
                self.x
            }
        }

        impl Sub for Widget {
            fn sub_val(&self) -> u32 {
                self.x + 10u32
            }
        }

        fn main() -> u32 {
            let w = Widget { x: 20u32 };
            let a = w.base_val();
            let w2 = Widget { x: 20u32 };
            let b = w2.sub_val();
            a + b - 8u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("supertrait impl should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    // 20 + 30 - 8 = 42
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_rejects_missing_supertrait_impl() {
    let source = r#"
        trait Base {
            fn base_val(&self) -> u32;
        }

        trait Sub: Base {
            fn sub_val(&self) -> u32;
        }

        struct Widget {
            x: u32,
        }

        impl Sub for Widget {
            fn sub_val(&self) -> u32 {
                self.x
            }
        }

        fn main() -> u32 { 0u32 }
    "#;

    let err = SourceProgram::parse(source).expect_err("missing supertrait impl should fail");

    match err {
        SourceError::Invalid { context, detail } => {
            assert_eq!(context, "impl");
            assert!(
                detail.contains("Base"),
                "error should mention missing supertrait Base, got: {detail}"
            );
            assert!(
                detail.contains("Widget"),
                "error should mention implementing type Widget, got: {detail}"
            );
        }
        other => panic!("expected invalid error for missing supertrait, got {other:?}"),
    }
}

#[test]
fn test_source_program_supertrait_multiple_bounds() {
    let source = r#"
        trait Alpha {
            fn alpha(&self) -> u32;
        }

        trait Beta {
            fn beta(&self) -> u32;
        }

        trait Gamma: Alpha + Beta {
            fn gamma(&self) -> u32;
        }

        struct Tri {
            v: u32,
        }

        impl Alpha for Tri {
            fn alpha(&self) -> u32 {
                self.v
            }
        }

        impl Beta for Tri {
            fn beta(&self) -> u32 {
                self.v + 1u32
            }
        }

        impl Gamma for Tri {
            fn gamma(&self) -> u32 {
                self.v + 2u32
            }
        }

        fn main() -> u32 {
            let t = Tri { v: 10u32 };
            let a = t.alpha();
            let t2 = Tri { v: 10u32 };
            let b = t2.beta();
            let t3 = Tri { v: 10u32 };
            let g = t3.gamma();
            a + b + g
        }
    "#;

    let program = SourceProgram::parse(source).expect("multiple supertrait impl should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    // 10 + 11 + 12 = 33
    assert_eq!(result.value(), Some(Value::u32(33)));
}

#[test]
fn test_source_program_supertrait_lifetime_bound_accepted() {
    // `trait Scoped: 'static` should parse without error — lifetime bounds are
    // not supertrait trait obligations, just lifetime constraints.
    let source = r#"
        trait Scoped: 'static {
            fn val(&self) -> u32;
        }

        struct Item {
            x: u32,
        }

        impl Scoped for Item {
            fn val(&self) -> u32 {
                self.x
            }
        }

        fn main() -> u32 {
            let i = Item { x: 42u32 };
            i.val()
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait with lifetime bound should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_supertrait_default_method_inheritance() {
    // Verify that a subtrait's impl can rely on the supertrait's methods
    // (both impls must exist, supertrait defaults flow through independently)
    let source = r#"
        trait Base {
            fn base_op(self, x: u32) -> u32 {
                x + 5u32
            }
        }

        trait Sub: Base {
            fn sub_op(&self) -> u32;
        }

        struct Widget {
            v: u32,
        }

        impl Base for Widget {}

        impl Sub for Widget {
            fn sub_op(&self) -> u32 {
                self.v
            }
        }

        fn main() -> u32 {
            let w = Widget { v: 37u32 };
            w.base_op(0u32)
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("supertrait with default methods should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    // base_op default: 0 + 5 = 5
    assert_eq!(result.value(), Some(Value::u32(5)));
}

#[test]
fn test_source_program_supertrait_registers_trait_def_with_supertraits() {
    let source = r#"
        trait Base {
            fn base_fn(&self) -> u32;
        }

        trait Sub: Base {
            fn sub_fn(&self) -> u32;
        }

        struct W { v: u32 }
        impl Base for W {
            fn base_fn(&self) -> u32 { self.v }
        }
        impl Sub for W {
            fn sub_fn(&self) -> u32 { self.v }
        }

        fn main() -> u32 { 0u32 }
    "#;

    let program = SourceProgram::parse(source).expect("should parse");
    // Verify the TraitDef has supertraits recorded
    let sub_def = program.items().iter().find_map(|item| {
        if let Item::TraitDef(def) = item {
            if def.name == "Sub" {
                return Some(def);
            }
        }
        None
    });
    let sub_def = sub_def.expect("Sub trait def should exist");
    assert_eq!(sub_def.supertraits, vec!["Base".to_string()]);
}
