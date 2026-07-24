// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{Interpreter, SourceError, SourceProgram, Value};
use clean_rust_sem::expr::Item;
use clean_rust_sem::stmt::GenericParam;
use clean_rust_sem::types::ReceiverMode;
use clean_rust_sem::{RustType, UintType};

#[test]
fn test_source_program_registers_trait_definitions() {
    let source = r#"
        trait Greeter {
            fn greet(&mut self, suffix: u32) -> u32;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait definition should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
    let trait_def = interpreter
        .ctx
        .get_trait_def("Greeter")
        .expect("trait definition should be registered");
    assert_eq!(trait_def.methods.len(), 1);
    assert_eq!(trait_def.methods[0].name, "greet");
    assert_eq!(trait_def.methods[0].receiver, ReceiverMode::ByMut);
    assert_eq!(
        trait_def.methods[0].params,
        vec![RustType::Uint(UintType::U32)]
    );
    assert_eq!(trait_def.methods[0].ret, RustType::Uint(UintType::U32));
}

#[test]
fn test_source_program_runs_unsafe_trait_impl_method() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        unsafe trait Marker {
            fn mark(self) -> u32;
        }

        unsafe impl Marker for Counter {
            fn mark(self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            Counter { value: 42u32 }.mark()
        }
    "#;

    let program = SourceProgram::parse(source).expect("unsafe trait impl should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_rejects_safe_impl_for_unsafe_trait() {
    let source = r#"
        struct Counter {
            value: u32,
        }

        unsafe trait Marker {
            fn mark(self) -> u32;
        }

        impl Marker for Counter {
            fn mark(self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            Counter { value: 42u32 }.mark()
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("safe impl for unsafe trait should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "impl");
            assert!(
                detail.contains("requires `unsafe impl`"),
                "detail should mention unsafe impl requirement, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

#[test]
fn test_source_program_registers_trait_definition_with_associated_types() {
    let source = r#"
        trait Iterator {
            type Item;
            type Label: Clone + 'static;
            type Output: ?Sized = u32;
            fn next(&mut self) -> u32;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("trait definition with associated types should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));

    let trait_def = interpreter
        .ctx
        .get_trait_def("Iterator")
        .expect("trait definition should be registered");

    assert_eq!(trait_def.associated_types.len(), 3);

    let item = &trait_def.associated_types[0];
    assert_eq!(item.name, "Item");
    assert!(item.bounds.is_empty());
    assert!(item.default.is_none());

    let label = &trait_def.associated_types[1];
    assert_eq!(label.name, "Label");
    assert_eq!(
        label.bounds,
        vec!["Clone".to_string(), "'static".to_string()]
    );
    assert!(label.default.is_none());

    let output = &trait_def.associated_types[2];
    assert_eq!(output.name, "Output");
    assert_eq!(output.bounds, vec!["?Sized".to_string()]);
    assert_eq!(output.default, Some(RustType::Uint(UintType::U32)));
}

#[test]
fn test_source_program_parses_generic_associated_type_definition() {
    let source = r#"
        trait Iterator {
            type Item<T>;
            fn next(&self) -> u32;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("generic associated type definition should parse");

    let trait_def = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::TraitDef(def) if def.name == "Iterator" => Some(def),
            _ => None,
        })
        .expect("Iterator trait should be present");
    let assoc = trait_def
        .associated_types
        .iter()
        .find(|assoc| assoc.name == "Item")
        .expect("Iterator::Item associated type should be present");

    assert_eq!(assoc.generic_params.len(), 1);
    match &assoc.generic_params[0] {
        GenericParam::Type(type_param) => assert_eq!(type_param.name, "T"),
        other => panic!("expected type generic parameter, got {other:?}"),
    }
}

#[test]
fn test_source_program_registers_trait_impl_associated_types() {
    let source = r#"
        trait Iterator {
            type Item;
            fn next(&mut self) -> u32;
        }

        struct Counter {
            value: u32,
        }

        impl Iterator for Counter {
            type Item = u32;

            fn next(&mut self) -> u32 {
                self.value
            }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("trait impl associated type should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));

    let impl_info = interpreter
        .ctx
        .get_trait_impl("Iterator", "Counter")
        .expect("trait impl should be registered");
    assert_eq!(
        impl_info
            .associated_types
            .get("Item")
            .map(|assoc| &assoc.ty),
        Some(&RustType::Uint(UintType::U32))
    );
}

#[test]
fn test_source_program_registers_generic_impl_associated_type() {
    let source = r#"
        trait Iterator {
            type Item<T>;
            fn next(&self) -> u32;
        }

        struct Counter;

        impl Iterator for Counter {
            type Item<T> = T;

            fn next(&self) -> u32 {
                42u32
            }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program = SourceProgram::parse(source).expect("generic impl associated type should parse");
    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);

    assert_eq!(result.value(), Some(Value::u32(42)));
    assert_eq!(
        interpreter.ctx.resolve_gat(
            &RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
            "Iterator",
            "Item",
            &[RustType::Uint(UintType::U32)],
            &[],
        ),
        Some(RustType::Uint(UintType::U32))
    );
}

#[test]
fn test_source_program_parses_qualified_associated_type_projection() {
    let source = r#"
        trait Iterator {
            type Item;
            fn next(&mut self) -> u32;
        }

        struct Counter;

        impl Iterator for Counter {
            type Item = u32;

            fn next(&mut self) -> u32 {
                42u32
            }
        }

        fn project(value: <Counter as Iterator>::Item) -> <Counter as Iterator>::Item {
            value
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("qualified associated type projection should parse");

    let project = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "project"))
        .expect("project function should be present");
    let (params, ret) = match project {
        Item::Fn { params, ret, .. } => (params, ret),
        _ => panic!("project should lower to a function item"),
    };

    let expected_self_ty = RustType::Named {
        name: "Counter".to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    };

    assert_eq!(params.len(), 1, "project should have one parameter");
    let (_, param_ty) = &params[0];
    assert_eq!(
        param_ty,
        &RustType::TypeProjection {
            self_ty: Box::new(expected_self_ty.clone()),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        }
    );
    assert_eq!(
        ret,
        &RustType::TypeProjection {
            self_ty: Box::new(expected_self_ty),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        }
    );

    let mut interpreter = Interpreter::new();
    let result = program.run(&mut interpreter);
    assert_eq!(result.value(), Some(Value::u32(42)));
}

#[test]
fn test_source_program_parses_projection_nested_in_generic_type() {
    let source = r#"
        trait Iterator {
            type Item;
            fn next(&mut self) -> u32;
        }

        struct Counter;

        impl Iterator for Counter {
            type Item = u32;

            fn next(&mut self) -> u32 {
                42u32
            }
        }

        fn take_option(_value: Option<<Counter as Iterator>::Item>) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let program =
        SourceProgram::parse(source).expect("nested qualified associated type should parse");

    let take_option = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "take_option"))
        .expect("take_option function should be present");
    let params = match take_option {
        Item::Fn { params, .. } => params,
        _ => panic!("take_option should lower to a function item"),
    };

    assert_eq!(params.len(), 1, "take_option should have one parameter");
    let (_, param_ty) = &params[0];
    assert_eq!(
        param_ty,
        &RustType::Option {
            inner: Box::new(RustType::TypeProjection {
                self_ty: Box::new(RustType::Named {
                    name: "Counter".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }),
                trait_name: "Iterator".to_string(),
                assoc_name: "Item".to_string(),
                assoc_type_args: vec![],
                assoc_lifetime_args: vec![],
                const_args: vec![],
            }),
        }
    );
}

#[test]
fn test_source_program_rejects_unqualified_qself_projection_type() {
    let source = r#"
        struct Counter;

        fn project(_value: <Counter>::Item) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let err = SourceProgram::parse(source).expect_err("unqualified qself projection should fail");

    match err {
        SourceError::Unsupported { context, detail } => {
            assert_eq!(context, "type");
            assert!(
                detail.contains("<T as Trait>::Assoc"),
                "detail should mention the supported projection form, got: {detail}"
            );
        }
        other => panic!("expected unsupported error, got {other:?}"),
    }
}

/// Extracts the single-parameter type of the function named `name`.
fn projection_param_ty(program: &SourceProgram, name: &str) -> RustType {
    let func = program
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name: n, .. } if n == name))
        .expect("function should be present");
    let params = match func {
        Item::Fn { params, .. } => params,
        _ => panic!("{name} should lower to a function item"),
    };
    assert_eq!(params.len(), 1, "{name} should have exactly one parameter");
    params[0].1.clone()
}

#[test]
fn test_source_program_parses_qself_projection_with_literal_const_arg() {
    use clean_rust_sem::types::{ConstGenericArg, ConstGenericValue};

    let source = r#"
        trait Buffer {
            type Slot;
            fn len(&self) -> u32;
        }

        struct Ring;

        impl Buffer for Ring {
            type Slot = u32;

            fn len(&self) -> u32 {
                0u32
            }
        }

        fn slot(_value: <Ring as Buffer>::Slot<8>) -> u32 {
            0u32
        }

        fn main() -> u32 {
            0u32
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("qself projection with a literal const argument should parse");

    let ty = projection_param_ty(&program, "slot");
    match ty {
        RustType::TypeProjection {
            trait_name,
            assoc_name,
            assoc_type_args,
            const_args,
            ..
        } => {
            assert_eq!(trait_name, "Buffer");
            assert_eq!(assoc_name, "Slot");
            assert!(
                assoc_type_args.is_empty(),
                "a const-only argument must not populate assoc_type_args"
            );
            assert_eq!(
                const_args,
                vec![ConstGenericArg::Value(ConstGenericValue::Usize(8))],
                "the literal const argument must be threaded into const_args"
            );
        }
        other => panic!("expected a type projection, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_qself_projection_with_type_and_const_arg_mix() {
    use clean_rust_sem::types::{ConstGenericArg, ConstGenericValue};

    let source = r#"
        trait Buffer {
            type Slot;
            fn len(&self) -> u32;
        }

        struct Ring;

        impl Buffer for Ring {
            type Slot = u32;

            fn len(&self) -> u32 {
                0u32
            }
        }

        fn slot(_value: <Ring as Buffer>::Slot<u32, 4>) -> u32 {
            0u32
        }

        fn main() -> u32 {
            0u32
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("qself projection mixing a type and const argument should parse");

    let ty = projection_param_ty(&program, "slot");
    match ty {
        RustType::TypeProjection {
            assoc_type_args,
            const_args,
            ..
        } => {
            assert_eq!(
                assoc_type_args,
                vec![RustType::Uint(UintType::U32)],
                "the type argument must land in assoc_type_args"
            );
            assert_eq!(
                const_args,
                vec![ConstGenericArg::Value(ConstGenericValue::Usize(4))],
                "the const argument must land in const_args"
            );
        }
        other => panic!("expected a type projection, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_qself_projection_with_const_param_arg() {
    use clean_rust_sem::types::ConstGenericArg;

    // A bare const parameter in a const-argument position must be braced
    // (`{N}`) so the Rust grammar treats it as a const, not a type, argument.
    let source = r#"
        trait Buffer {
            type Slot;
            fn len(&self) -> u32;
        }

        struct Ring<const N: usize>;

        impl<const N: usize> Buffer for Ring<N> {
            type Slot = u32;

            fn len(&self) -> u32 {
                0u32
            }
        }

        impl<const N: usize> Ring<N> {
            fn slot(&self, _value: <Ring<N> as Buffer>::Slot<{ N }>) -> u32 {
                0u32
            }
        }

        fn main() -> u32 {
            0u32
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("qself projection with a const-parameter argument should parse");

    let impl_items = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::Impl {
                trait_name: None,
                items,
                ..
            } => Some(items),
            _ => None,
        })
        .expect("inherent impl should be present");
    let slot = impl_items
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "slot"))
        .expect("slot method should be present");
    let params = match slot {
        Item::Fn { params, .. } => params,
        _ => panic!("slot should lower to a function item"),
    };
    let value_ty = &params
        .iter()
        .find(|(name, _)| name == "_value")
        .expect("slot should take a _value parameter")
        .1;

    match value_ty {
        RustType::TypeProjection {
            assoc_name,
            const_args,
            ..
        } => {
            assert_eq!(assoc_name, "Slot");
            assert_eq!(
                const_args,
                &vec![ConstGenericArg::Param("N".to_string())],
                "the braced const parameter must be threaded into const_args"
            );
        }
        other => panic!("expected a type projection, got {other:?}"),
    }
}

#[test]
fn test_source_program_parses_self_projection_with_const_arg() {
    use clean_rust_sem::types::{ConstGenericArg, ConstGenericValue};

    let source = r#"
        trait Buffer {
            type Slot;
            fn first(&self) -> Self::Slot<2>;
        }

        fn main() -> u32 {
            0u32
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("Self::Assoc projection with a const argument should parse");

    let trait_def = program
        .items()
        .iter()
        .find_map(|item| match item {
            Item::TraitDef(def) if def.name == "Buffer" => Some(def),
            _ => None,
        })
        .expect("Buffer trait should be present");
    let method = trait_def
        .methods
        .iter()
        .find(|method| method.name == "first")
        .expect("first method should be present");

    match &method.ret {
        RustType::TypeProjection {
            trait_name,
            assoc_name,
            const_args,
            ..
        } => {
            assert_eq!(trait_name, "Buffer");
            assert_eq!(assoc_name, "Slot");
            assert_eq!(
                const_args,
                &vec![ConstGenericArg::Value(ConstGenericValue::Usize(2))],
                "the const argument on a Self projection must be threaded into const_args"
            );
        }
        other => panic!("expected a type projection, got {other:?}"),
    }
}

#[test]
fn test_source_program_qself_projection_without_const_arg_has_empty_const_args() {
    let source = r#"
        trait Buffer {
            type Slot;
            fn len(&self) -> u32;
        }

        struct Ring;

        impl Buffer for Ring {
            type Slot = u32;

            fn len(&self) -> u32 {
                0u32
            }
        }

        fn slot(_value: <Ring as Buffer>::Slot) -> u32 {
            0u32
        }

        fn main() -> u32 {
            0u32
        }
    "#;

    let program = SourceProgram::parse(source)
        .expect("qself projection without const arguments should still parse");

    let ty = projection_param_ty(&program, "slot");
    match ty {
        RustType::TypeProjection {
            assoc_type_args,
            assoc_lifetime_args,
            const_args,
            ..
        } => {
            assert!(assoc_type_args.is_empty());
            assert!(assoc_lifetime_args.is_empty());
            assert!(
                const_args.is_empty(),
                "no-const-argument projections must keep const_args empty (no regression)"
            );
        }
        other => panic!("expected a type projection, got {other:?}"),
    }
}
