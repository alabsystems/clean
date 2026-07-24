// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_rust_sem::expr::Item;

use super::SourceProgram;

// ── Generic trait bound on type parameter ───────────────────────────

#[test]
fn test_source_program_accepts_generic_trait_bound_on_type_param() {
    let source = r#"
        fn consume<T: Iterator<Item = u32>>(_value: T) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog = SourceProgram::parse(source).expect("generic trait bound should parse");
    let fn_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "consume"))
        .expect("consume function should exist");

    if let Item::Fn { type_params, .. } = fn_item {
        assert_eq!(type_params.len(), 1);
        assert_eq!(type_params[0].name, "T");
        assert_eq!(
            type_params[0].bounds,
            vec!["Iterator".to_string()],
            "bound should store the trait name without generic arguments"
        );
    } else {
        panic!("expected Fn item");
    }
}

// ── Generic trait bound in where clause ─────────────────────────────

#[test]
fn test_source_program_accepts_generic_trait_bound_in_where_clause() {
    let source = r#"
        fn consume<T>(_value: T) -> u32
        where
            T: Into<Option<u32>>,
        {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog = SourceProgram::parse(source).expect("where-clause generic bound should parse");
    let fn_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "consume"))
        .expect("consume function should exist");

    if let Item::Fn { type_params, .. } = fn_item {
        assert_eq!(type_params.len(), 1);
        assert_eq!(type_params[0].name, "T");
        assert_eq!(
            type_params[0].bounds,
            vec!["Into".to_string()],
            "where-clause bound should store the trait name without generic arguments"
        );
    } else {
        panic!("expected Fn item");
    }
}

// ── Generic supertrait ──────────────────────────────────────────────

#[test]
fn test_source_program_accepts_generic_supertrait() {
    let source = r#"
        trait Base<T> {
            fn base(&self) -> u32;
        }

        trait Derived: Base<u32> {
            fn derived(&self) -> u32;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog = SourceProgram::parse(source).expect("generic supertrait should parse");
    let trait_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(def) if def.name == "Derived"))
        .expect("Derived trait should exist");

    if let Item::TraitDef(def) = trait_item {
        assert_eq!(
            def.supertraits,
            vec!["Base".to_string()],
            "supertrait should store name without generic arguments"
        );
    } else {
        panic!("expected TraitDef item");
    }
}

// ── Generic trait impl header ───────────────────────────────────────

#[test]
fn test_source_program_accepts_generic_trait_impl_header() {
    let source = r#"
        trait Show<T> {
            fn show(&self) -> u32;
        }

        struct Counter;

        impl Show<u32> for Counter {
            fn show(&self) -> u32 {
                42u32
            }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog = SourceProgram::parse(source).expect("generic trait impl header should parse");
    let impl_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::Impl { trait_name: Some(name), .. } if name == "Show"))
        .expect("impl Show for Counter should exist");

    if let Item::Impl { trait_name, .. } = impl_item {
        assert_eq!(
            trait_name.as_deref(),
            Some("Show"),
            "impl trait_name should store name without generic arguments"
        );
    } else {
        panic!("expected Impl item");
    }
}

// ── Generic dyn trait bound ─────────────────────────────────────────

#[test]
fn test_source_program_accepts_generic_dyn_trait_bound() {
    let source = r#"
        trait Iterator {
            type Item;
            fn next(&mut self) -> u32;
        }

        fn takes(_iter: &dyn Iterator<Item = u32>) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog =
        SourceProgram::parse(source).expect("dyn trait bound with generic args should parse");
    let fn_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "takes"))
        .expect("takes function should exist");

    // The parameter type should be &dyn Iterator (name only, no generic args stored)
    assert!(
        matches!(fn_item, Item::Fn { .. }),
        "takes should be a function"
    );
}

// ── Generic impl Trait bound ────────────────────────────────────────

#[test]
fn test_source_program_accepts_generic_impl_trait_bound() {
    let source = r#"
        trait Iterator {
            type Item;
            fn next(&mut self) -> u32;
        }

        fn takes(_iter: impl Iterator<Item = u32>) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog =
        SourceProgram::parse(source).expect("impl trait bound with generic args should parse");
    let fn_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "takes"))
        .expect("takes function should exist");

    assert!(
        matches!(fn_item, Item::Fn { .. }),
        "takes should be a function"
    );
}

// ── End-to-end: generic bound on associated type in trait ───────────

#[test]
fn test_source_program_accepts_associated_type_with_generic_bound() {
    let source = r#"
        trait Processor {
            type Output: Into<u32>;
            fn process(&self) -> u32;
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog =
        SourceProgram::parse(source).expect("associated type with generic-arg bound should parse");
    let trait_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::TraitDef(def) if def.name == "Processor"))
        .expect("Processor trait should exist");

    if let Item::TraitDef(def) = trait_item {
        assert_eq!(def.associated_types.len(), 1);
        assert_eq!(def.associated_types[0].name, "Output");
        assert_eq!(
            def.associated_types[0].bounds,
            vec!["Into".to_string()],
            "associated type bound should store trait name without generic arguments"
        );
    } else {
        panic!("expected TraitDef item");
    }
}

// ── Multiple generic bounds on type param ───────────────────────────

#[test]
fn test_source_program_accepts_multiple_generic_bounds() {
    let source = r#"
        fn consume<T: Clone + Into<u32>>(_value: T) -> u32 {
            42u32
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog = SourceProgram::parse(source).expect("multiple generic bounds should parse");
    let fn_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::Fn { name, .. } if name == "consume"))
        .expect("consume function should exist");

    if let Item::Fn { type_params, .. } = fn_item {
        assert_eq!(type_params[0].bounds.len(), 2);
        assert_eq!(type_params[0].bounds[0], "Clone");
        assert_eq!(type_params[0].bounds[1], "Into");
    } else {
        panic!("expected Fn item");
    }
}

// ── From<T> impl (common stdlib pattern) ────────────────────────────

#[test]
fn test_source_program_accepts_from_trait_impl() {
    let source = r#"
        trait From<T> {
            fn from(value: T) -> u32;
        }

        struct MyNum;

        impl From<u32> for MyNum {
            fn from(_value: u32) -> u32 {
                42u32
            }
        }

        fn main() -> u32 {
            42u32
        }
    "#;

    let prog = SourceProgram::parse(source).expect("From<u32> impl should parse");
    let impl_item = prog
        .items()
        .iter()
        .find(|item| matches!(item, Item::Impl { trait_name: Some(name), .. } if name == "From"))
        .expect("impl From<u32> for MyNum should exist");

    if let Item::Impl {
        trait_name,
        items: impl_items,
        ..
    } = impl_item
    {
        assert_eq!(trait_name.as_deref(), Some("From"));
        assert_eq!(impl_items.len(), 1);
    } else {
        panic!("expected Impl item");
    }
}
