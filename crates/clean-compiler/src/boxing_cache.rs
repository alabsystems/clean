// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Auxiliary declaration cache for the boxing pass.
//!
//! When the boxing pass creates helper declarations (e.g., box/unbox wrappers
//! for expensive constants), identical declarations should be deduplicated.
//! This module provides [`BoxingAuxCache`] to store and reuse auxiliary
//! declarations keyed by their content (base name + type signature).
//!
//! Part of #1054.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};

use crate::ir::{FnId, IRDecl, IRType};
use clean_kernel::Name;

/// Cache key for boxing auxiliary declarations.
///
/// Two auxiliary declarations are considered identical when they share the
/// same base name and full type signature (parameter types + return type).
#[derive(Clone, Debug)]
pub struct BoxingAuxKey {
    /// Base function name that the auxiliary is derived from.
    pub base_name: Name,
    /// Parameter types of the auxiliary declaration.
    pub param_types: Vec<IRType>,
    /// Return type of the auxiliary declaration.
    pub return_type: IRType,
}

/// Discriminant value for [`IRType`] used in hashing.
///
/// [`IRType`] derives `Eq` but not `Hash`. This function maps each variant to
/// a unique `u8` so that [`BoxingAuxKey`] can participate in hash-based
/// collections without requiring a `Hash` impl on `IRType` itself.
fn ir_type_discriminant(ty: &IRType) -> u8 {
    match ty {
        IRType::Bool => 0,
        IRType::UInt8 => 1,
        IRType::UInt16 => 2,
        IRType::UInt32 => 3,
        IRType::UInt64 => 4,
        IRType::USize => 5,
        IRType::Float32 => 6,
        IRType::Float64 => 7,
        IRType::Object => 8,
        IRType::TObject => 9,
        IRType::Struct(_) => 10,
        IRType::Union(_) => 11,
        IRType::Erased => 12,
        IRType::Void => 13,
    }
}

/// Hash an [`IRType`] into a [`Hasher`].
///
/// Recursively hashes composite types (Struct, Union) by their element
/// discriminants. This is consistent with `PartialEq`: equal types produce
/// equal hashes.
fn hash_ir_type<H: Hasher>(ty: &IRType, state: &mut H) {
    ir_type_discriminant(ty).hash(state);
    match ty {
        IRType::Struct(fields) => {
            fields.len().hash(state);
            for f in fields {
                hash_ir_type(f, state);
            }
        }
        IRType::Union(variants) => {
            variants.len().hash(state);
            for v in variants {
                hash_ir_type(v, state);
            }
        }
        _ => {}
    }
}

impl PartialEq for BoxingAuxKey {
    fn eq(&self, other: &Self) -> bool {
        self.base_name == other.base_name
            && self.return_type == other.return_type
            && self.param_types == other.param_types
    }
}

impl Eq for BoxingAuxKey {}

impl Hash for BoxingAuxKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.base_name.hash(state);
        self.param_types.len().hash(state);
        for ty in &self.param_types {
            hash_ir_type(ty, state);
        }
        hash_ir_type(&self.return_type, state);
    }
}

/// Cache for deduplicating boxing auxiliary declarations.
///
/// When the boxing pass encounters an expensive constant or wrapper that
/// requires a helper declaration, this cache ensures that identical helpers
/// are created only once. Subsequent requests for the same key return the
/// previously generated [`FnId`].
///
/// # Usage
///
/// ```text
/// let mut cache = BoxingAuxCache::new();
/// let key = BoxingAuxKey {
///     base_name: Name::from_string("Nat.add"),
///     param_types: vec![],
///     return_type: IRType::Object,
/// };
/// let fn_id = cache.get_or_insert(&key, |name| IRDecl {
///     name,
///     params: vec![],
///     return_type: IRType::Object,
///     body: /* ... */,
/// });
/// // Second call with same key returns the same FnId without creating a new decl.
/// let fn_id2 = cache.get_or_insert(&key, |_| panic!("should not be called"));
/// assert_eq!(fn_id, fn_id2);
/// ```
pub struct BoxingAuxCache {
    /// Maps cache keys to the index of the generated declaration in `decls`.
    index: HashMap<BoxingAuxKey, usize>,
    /// All generated auxiliary declarations, in insertion order.
    decls: Vec<IRDecl>,
    /// Monotonic counter for generating unique auxiliary name suffixes.
    next_id: u32,
}

impl BoxingAuxCache {
    /// Create an empty auxiliary declaration cache.
    #[must_use]
    pub fn new() -> Self {
        Self {
            index: HashMap::new(),
            decls: Vec::new(),
            next_id: 0,
        }
    }

    /// Look up or create an auxiliary declaration for the given key.
    ///
    /// If a declaration matching `key` already exists in the cache, its
    /// [`FnId`] is returned immediately and `make_decl` is **not** called.
    ///
    /// Otherwise, a fresh [`Name`] is generated (by appending a unique suffix
    /// to `key.base_name`), passed to `make_decl` to construct the [`IRDecl`],
    /// and the result is cached for future lookups.
    ///
    /// # Arguments
    ///
    /// * `key` - Identifies the auxiliary declaration by base name + type sig.
    /// * `make_decl` - Closure that builds the [`IRDecl`] given a fresh name.
    ///   Only called on cache miss.
    #[must_use]
    pub fn get_or_insert(
        &mut self,
        key: &BoxingAuxKey,
        make_decl: impl FnOnce(Name) -> IRDecl,
    ) -> FnId {
        if let Some(&idx) = self.index.get(key) {
            return FnId(self.decls[idx].name.clone());
        }
        let fresh_name = self.fresh_name(&key.base_name);
        let decl = make_decl(fresh_name);
        let fn_id = FnId(decl.name.clone());
        let idx = self.decls.len();
        self.decls.push(decl);
        self.index.insert(key.clone(), idx);
        fn_id
    }

    /// Return the number of cached auxiliary declarations.
    #[must_use]
    pub fn len(&self) -> usize {
        self.decls.len()
    }

    /// Return whether the cache is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.decls.is_empty()
    }

    /// Consume the cache and return all generated auxiliary declarations.
    ///
    /// Declarations are returned in insertion order, suitable for prepending
    /// to the module's declaration list.
    #[must_use]
    pub fn into_decls(self) -> Vec<IRDecl> {
        self.decls
    }

    /// Generate a fresh unique name derived from `base`.
    fn fresh_name(&mut self, base: &Name) -> Name {
        let id = self.next_id;
        self.next_id += 1;
        base.clone().str(format!("_boxing_aux_{}", id))
    }
}

impl Default for BoxingAuxCache {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{IRArg, IRBody, IRExpr, IRType, VarId};

    fn make_simple_decl(name: Name, return_type: IRType) -> IRDecl {
        IRDecl {
            name,
            params: vec![],
            return_type,
            body: IRBody::Ret(IRArg::Erased),
        }
    }

    fn make_key(base: &str, param_types: Vec<IRType>, return_type: IRType) -> BoxingAuxKey {
        BoxingAuxKey {
            base_name: Name::from_string(base),
            param_types,
            return_type,
        }
    }

    #[test]
    fn test_cache_new_is_empty() {
        let cache = BoxingAuxCache::new();
        assert!(cache.is_empty());
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_cache_insert_returns_fn_id() {
        let mut cache = BoxingAuxCache::new();
        let key = make_key("foo", vec![], IRType::Object);
        let fn_id = cache.get_or_insert(&key, |name| make_simple_decl(name, IRType::Object));
        assert!(!cache.is_empty());
        assert_eq!(cache.len(), 1);
        // The returned FnId should reference the generated name
        let decls = cache.into_decls();
        assert_eq!(decls.len(), 1);
        assert_eq!(FnId(decls[0].name.clone()), fn_id);
    }

    #[test]
    fn test_cache_deduplicates_identical_keys() {
        let mut cache = BoxingAuxCache::new();
        let key = make_key("bar", vec![IRType::UInt64], IRType::Object);
        let fn_id1 = cache.get_or_insert(&key, |name| IRDecl {
            name,
            params: vec![(VarId(0), IRType::UInt64)],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(0),
                ty: IRType::Object,
                value: IRExpr::Box {
                    ty: IRType::UInt64,
                    arg: IRArg::Var(VarId(0)),
                },
                rest: Box::new(IRBody::Ret(IRArg::Var(VarId(0)))),
            },
        });
        let call_count = std::cell::Cell::new(0);
        let fn_id2 = cache.get_or_insert(&key, |name| {
            call_count.set(call_count.get() + 1);
            make_simple_decl(name, IRType::Object)
        });
        assert_eq!(fn_id1, fn_id2, "same key should return same FnId");
        assert_eq!(call_count.get(), 0, "make_decl should not be called on hit");
        assert_eq!(cache.len(), 1, "only one decl should exist");
    }

    #[test]
    fn test_cache_different_keys_produce_different_decls() {
        let mut cache = BoxingAuxCache::new();
        let key_u64 = make_key("baz", vec![], IRType::UInt64);
        let key_u32 = make_key("baz", vec![], IRType::UInt32);
        let fn_id1 = cache.get_or_insert(&key_u64, |name| make_simple_decl(name, IRType::UInt64));
        let fn_id2 = cache.get_or_insert(&key_u32, |name| make_simple_decl(name, IRType::UInt32));
        assert_ne!(fn_id1, fn_id2, "different return types => different FnIds");
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_cache_different_base_names_not_deduplicated() {
        let mut cache = BoxingAuxCache::new();
        let key_a = make_key("alpha", vec![], IRType::Object);
        let key_b = make_key("beta", vec![], IRType::Object);
        let fn_id_a = cache.get_or_insert(&key_a, |name| make_simple_decl(name, IRType::Object));
        let fn_id_b = cache.get_or_insert(&key_b, |name| make_simple_decl(name, IRType::Object));
        assert_ne!(fn_id_a, fn_id_b);
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_cache_different_param_types_not_deduplicated() {
        let mut cache = BoxingAuxCache::new();
        let key1 = make_key("f", vec![IRType::UInt64], IRType::Object);
        let key2 = make_key("f", vec![IRType::UInt32], IRType::Object);
        let key3 = make_key("f", vec![IRType::UInt64, IRType::Bool], IRType::Object);
        let id1 = cache.get_or_insert(&key1, |n| make_simple_decl(n, IRType::Object));
        let id2 = cache.get_or_insert(&key2, |n| make_simple_decl(n, IRType::Object));
        let id3 = cache.get_or_insert(&key3, |n| make_simple_decl(n, IRType::Object));
        assert_ne!(id1, id2);
        assert_ne!(id1, id3);
        assert_ne!(id2, id3);
        assert_eq!(cache.len(), 3);
    }

    #[test]
    fn test_cache_fresh_names_are_unique() {
        let mut cache = BoxingAuxCache::new();
        let key1 = make_key("g", vec![], IRType::UInt64);
        let key2 = make_key("g", vec![], IRType::UInt32);
        let key3 = make_key("g", vec![], IRType::Bool);
        let id1 = cache.get_or_insert(&key1, |n| make_simple_decl(n, IRType::UInt64));
        let id2 = cache.get_or_insert(&key2, |n| make_simple_decl(n, IRType::UInt32));
        let id3 = cache.get_or_insert(&key3, |n| make_simple_decl(n, IRType::Bool));
        // All three names should be distinct
        let decls = cache.into_decls();
        let names: Vec<_> = decls.iter().map(|d| d.name.clone()).collect();
        assert_ne!(names[0], names[1]);
        assert_ne!(names[0], names[2]);
        assert_ne!(names[1], names[2]);
        // And the FnIds should match
        assert_eq!(FnId(names[0].clone()), id1);
        assert_eq!(FnId(names[1].clone()), id2);
        assert_eq!(FnId(names[2].clone()), id3);
    }

    #[test]
    fn test_cache_into_decls_preserves_insertion_order() {
        let mut cache = BoxingAuxCache::new();
        let keys: Vec<_> = (0..5)
            .map(|i| make_key(&format!("fn_{}", i), vec![], IRType::Object))
            .collect();
        let ids: Vec<_> = keys
            .iter()
            .map(|k| cache.get_or_insert(k, |n| make_simple_decl(n, IRType::Object)))
            .collect();
        let decls = cache.into_decls();
        assert_eq!(decls.len(), 5);
        for (decl, expected_id) in decls.iter().zip(ids.iter()) {
            assert_eq!(&FnId(decl.name.clone()), expected_id);
        }
    }

    #[test]
    fn test_cache_default_is_empty() {
        let cache = BoxingAuxCache::default();
        assert!(cache.is_empty());
    }

    #[test]
    fn test_key_equality_struct_types() {
        let key1 = make_key(
            "h",
            vec![IRType::Struct(vec![IRType::UInt64, IRType::Bool])],
            IRType::Object,
        );
        let key2 = make_key(
            "h",
            vec![IRType::Struct(vec![IRType::UInt64, IRType::Bool])],
            IRType::Object,
        );
        let key3 = make_key(
            "h",
            vec![IRType::Struct(vec![IRType::UInt32, IRType::Bool])],
            IRType::Object,
        );
        assert_eq!(key1, key2);
        assert_ne!(key1, key3);

        // Hash consistency: equal keys must hash equally
        let hash1 = {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            key1.hash(&mut h);
            h.finish()
        };
        let hash2 = {
            let mut h = std::collections::hash_map::DefaultHasher::new();
            key2.hash(&mut h);
            h.finish()
        };
        assert_eq!(hash1, hash2, "equal keys must produce equal hashes");
    }

    #[test]
    fn test_key_equality_union_types() {
        let key1 = make_key("u", vec![IRType::Union(vec![IRType::UInt64])], IRType::Void);
        let key2 = make_key("u", vec![IRType::Union(vec![IRType::UInt64])], IRType::Void);
        assert_eq!(key1, key2);
    }

    #[test]
    fn test_cache_with_realistic_boxing_decl() {
        let mut cache = BoxingAuxCache::new();
        let key = make_key("Nat.add", vec![], IRType::Object);
        let fn_id = cache.get_or_insert(&key, |name| IRDecl {
            name,
            params: vec![],
            return_type: IRType::Object,
            body: IRBody::VDecl {
                var: VarId(0),
                ty: IRType::UInt64,
                value: IRExpr::Lit(crate::ir::IRLiteral::UInt64(42)),
                rest: Box::new(IRBody::VDecl {
                    var: VarId(1),
                    ty: IRType::Object,
                    value: IRExpr::Box {
                        ty: IRType::UInt64,
                        arg: IRArg::Var(VarId(0)),
                    },
                    rest: Box::new(IRBody::Ret(IRArg::Var(VarId(1)))),
                }),
            },
        });
        // Re-inserting the same key should return the same FnId
        let fn_id2 =
            cache.get_or_insert(&key, |_| panic!("should not be called for duplicate key"));
        assert_eq!(fn_id, fn_id2);
        let decls = cache.into_decls();
        assert_eq!(decls.len(), 1);
        assert_eq!(decls[0].return_type, IRType::Object);
    }
}
