// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Virtual dispatch tables and type-name resolution context.

use std::collections::{BTreeMap, HashMap};

use crate::stmt::TraitImplInfo;

use super::definitions::{FunctionSignature, StructDef};
use super::{Lifetime, RustType};

/// Virtual table for dynamic dispatch
///
/// Represents the vtable pointer component of a trait object (`dyn Trait`).
/// The vtable maps trait method names to their concrete implementations
/// for a specific type.
///
/// Reference: Rust Reference, "Trait objects" section
/// <https://doc.rust-lang.org/reference/types/trait-object.html>
#[derive(Debug, Clone, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
pub struct VTable {
    /// Name of the trait this vtable implements
    pub trait_name: String,
    /// Trait method signatures (for type checking)
    pub methods: Vec<FunctionSignature>,
    /// Mapping from trait method name to concrete implementation function name
    pub impl_methods: BTreeMap<String, String>,
    /// The concrete type that implements this trait
    pub concrete_type: String,
}

impl VTable {
    /// Create a new vtable for a trait implementation
    #[must_use]
    pub fn new(trait_name: String, concrete_type: String) -> Self {
        Self {
            trait_name,
            methods: Vec::new(),
            impl_methods: BTreeMap::new(),
            concrete_type,
        }
    }

    /// Add a method mapping
    ///
    /// # Panics
    /// Panics if `trait_method` doesn't match `sig.name`. This catches
    /// programming errors where the method name is inconsistent.
    pub fn add_method(&mut self, trait_method: String, impl_fn: String, sig: FunctionSignature) {
        assert_eq!(
            trait_method, sig.name,
            "trait_method '{}' must match sig.name '{}'",
            trait_method, sig.name
        );
        self.methods.push(sig);
        self.impl_methods.insert(trait_method, impl_fn);
    }

    /// Look up the implementation function for a trait method
    #[must_use]
    pub fn get_impl(&self, method_name: &str) -> Option<&String> {
        self.impl_methods.get(method_name)
    }

    /// Look up the signature for a trait method
    #[must_use]
    pub fn get_signature(&self, method_name: &str) -> Option<&FunctionSignature> {
        self.methods.iter().find(|sig| sig.name == method_name)
    }
}

/// Type context for name resolution
#[derive(Debug, Clone, Default)]
pub struct TypeContext {
    pub structs: HashMap<String, StructDef>,
    pub enums: HashMap<String, super::EnumDef>,
    pub type_aliases: HashMap<String, RustType>,
    /// Trait implementations keyed by self type, then trait name.
    ///
    /// This mirrors the trait impl registry used by execution-time
    /// normalization so exported type resolution can answer associated-type
    /// and GAT projections directly.
    pub trait_impls: HashMap<String, HashMap<String, TraitImplInfo>>,
}

impl TypeContext {
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Resolve a named type to its definition
    #[must_use]
    pub fn resolve_type(&self, name: &str) -> Option<&StructDef> {
        self.structs.get(name)
    }

    /// Get size of a named type
    #[must_use]
    pub fn named_type_size(&self, name: &str) -> Option<usize> {
        self.structs.get(name).and_then(StructDef::size)
    }

    /// Resolve a generic associated type projection to its concrete type.
    ///
    /// This applies generic bindings from the concrete `self_ty` and then
    /// instantiates any generic parameters declared on the associated type.
    #[must_use]
    pub fn resolve_gat(
        &self,
        self_ty: &RustType,
        trait_name: &str,
        assoc_name: &str,
        type_args: &[RustType],
        lifetime_args: &[Lifetime],
    ) -> Option<RustType> {
        let type_name = self_ty.name()?;
        self.trait_impls
            .get(&type_name)
            .and_then(|impls| impls.get(trait_name))
            .and_then(|info| {
                info.resolve_associated_type(self_ty, assoc_name, type_args, lifetime_args)
            })
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::TypeContext;
    use crate::stmt::{AssociatedTypeValue, GenericParam, TraitImplInfo};
    use crate::types::{IntType, Lifetime, Mutability, RustType, TypeParamDef, TypeVar};

    #[test]
    fn test_type_context_resolve_gat_simple() {
        let mut ctx = TypeContext::new();
        let self_ty = RustType::Named {
            name: "Bar".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        };
        let item_param = TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        };

        ctx.trait_impls
            .entry("Bar".to_string())
            .or_default()
            .insert(
                "Foo".to_string(),
                TraitImplInfo {
                    trait_name: "Foo".to_string(),
                    self_ty: self_ty.clone(),
                    methods: HashMap::new(),
                    associated_types: HashMap::from([(
                        "Item".to_string(),
                        AssociatedTypeValue {
                            generic_params: vec![GenericParam::type_param(item_param.clone())],
                            where_clause: vec![],
                            ty: RustType::Option {
                                inner: Box::new(RustType::TypeParam(TypeVar {
                                    id: item_param.id,
                                    name: Some(item_param.name.clone()),
                                })),
                            },
                        },
                    )]),
                },
            );

        assert_eq!(
            ctx.resolve_gat(&self_ty, "Foo", "Item", &[RustType::Int(IntType::I32)], &[]),
            Some(RustType::Option {
                inner: Box::new(RustType::Int(IntType::I32)),
            })
        );
    }

    #[test]
    fn test_type_context_resolve_gat_generic_container() {
        let mut ctx = TypeContext::new();
        let container_param = TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        };

        ctx.trait_impls
            .entry("Container".to_string())
            .or_default()
            .insert(
                "LendingIterator".to_string(),
                TraitImplInfo {
                    trait_name: "LendingIterator".to_string(),
                    self_ty: RustType::Named {
                        name: "Container".to_string(),
                        type_args: vec![RustType::TypeParam(TypeVar {
                            id: container_param.id,
                            name: Some(container_param.name.clone()),
                        })],
                        lifetime_args: vec![],
                        const_args: vec![],
                    },
                    methods: HashMap::new(),
                    associated_types: HashMap::from([(
                        "Item".to_string(),
                        AssociatedTypeValue {
                            generic_params: vec![GenericParam::lifetime("a")],
                            where_clause: vec![],
                            ty: RustType::Reference {
                                lifetime: Lifetime::Named("a".to_string()),
                                mutability: Mutability::Shared,
                                inner: Box::new(RustType::TypeParam(TypeVar {
                                    id: container_param.id,
                                    name: Some(container_param.name.clone()),
                                })),
                            },
                        },
                    )]),
                },
            );

        let concrete_self = RustType::Named {
            name: "Container".to_string(),
            type_args: vec![RustType::Int(IntType::I32)],
            lifetime_args: vec![],
            const_args: vec![],
        };
        assert_eq!(
            ctx.resolve_gat(
                &concrete_self,
                "LendingIterator",
                "Item",
                &[],
                &[Lifetime::Named("iter".to_string())],
            ),
            Some(RustType::Reference {
                lifetime: Lifetime::Named("iter".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Int(IntType::I32)),
            })
        );
    }
}
