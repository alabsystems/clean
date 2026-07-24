// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::memory::{Address, AllocId};
use crate::types::Lifetime;
use std::collections::BTreeMap;

fn anon_lifetime() -> Lifetime {
    Lifetime::Anonymous(0)
}

fn shared_ref(inner: RustType) -> RustType {
    RustType::Reference {
        lifetime: anon_lifetime(),
        mutability: Mutability::Shared,
        inner: Box::new(inner),
    }
}

fn mut_ref(inner: RustType) -> RustType {
    RustType::Reference {
        lifetime: anon_lifetime(),
        mutability: Mutability::Mutable,
        inner: Box::new(inner),
    }
}

fn named_type(name: &str) -> RustType {
    RustType::Named {
        name: name.to_string(),
        type_args: vec![],
        lifetime_args: vec![],
        const_args: vec![],
    }
}

fn dyn_trait(name: &str) -> RustType {
    RustType::DynTrait {
        trait_name: name.to_string(),
        auto_traits: vec![],
    }
}

#[test]
fn test_ref_to_dyn_trait() {
    let from = shared_ref(named_type("Dog"));
    let to = shared_ref(dyn_trait("Animal"));

    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::UnsizeToDynTrait));
}

#[test]
fn test_mut_ref_to_shared_dyn_trait() {
    let from = mut_ref(named_type("Dog"));
    let to = shared_ref(dyn_trait("Animal"));

    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::UnsizeToDynTrait));
}

#[test]
fn test_shared_ref_to_mut_dyn_trait_rejected() {
    let from = shared_ref(named_type("Dog"));
    let to = mut_ref(dyn_trait("Animal"));

    assert_eq!(try_coerce(&from, &to), None);
}

#[test]
fn test_box_to_dyn_trait() {
    let from = RustType::Box {
        inner: Box::new(named_type("Dog")),
    };
    let to = RustType::Box {
        inner: Box::new(dyn_trait("Animal")),
    };

    assert_eq!(try_coerce(&from, &to), Some(CoercionKind::UnsizeToDynTrait));
}

#[test]
fn test_dyn_trait_upcast_is_not_treated_as_unsize() {
    let from = shared_ref(dyn_trait("Pet"));
    let to = shared_ref(dyn_trait("Animal"));

    assert_eq!(try_coerce(&from, &to), None);
}

#[test]
fn test_deref_then_unsize_to_dyn_trait() {
    let from = shared_ref(RustType::Box {
        inner: Box::new(named_type("Dog")),
    });
    let to = shared_ref(dyn_trait("Animal"));

    assert_eq!(
        try_coerce(&from, &to),
        Some(CoercionKind::Transitive(vec![
            CoercionKind::DerefCoercion {
                source: "Box".to_string(),
            },
            CoercionKind::UnsizeToDynTrait,
        ]))
    );
}

#[test]
fn test_coerce_value_dyn_trait_unsize_defers_to_runtime() {
    let value = Value::Reference {
        addr: Address::new(AllocId(9), 0),
        mutability: Mutability::Shared,
        lifetime: anon_lifetime(),
        referent: Some(Box::new(Value::Struct {
            name: "Dog".to_string(),
            fields: BTreeMap::new(),
        })),
    };
    let from = shared_ref(named_type("Dog"));
    let to = shared_ref(dyn_trait("Animal"));

    assert_eq!(coerce_value(&value, &from, &to), None);
}
