// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Property queries on `RustType`: size, copyability, compatibility,
//! thread-safety markers, and display name.

use super::{Lifetime, Mutability, RustType};

impl RustType {
    /// Size of the type in bytes (None for unsized types)
    pub fn size(&self) -> Option<usize> {
        match self {
            RustType::Unit | RustType::Never => Some(0),
            RustType::Bool => Some(1),
            RustType::Char => Some(4),
            RustType::Uint(u) => Some(u.size()),
            RustType::Int(i) => Some(i.size()),
            RustType::Float(f) => Some(f.size()),
            RustType::Atomic { inner } => inner.size(),
            // Thin pointers are 8 bytes on 64-bit; pointers to DSTs are fat pointers.
            RustType::Reference { inner, .. }
            | RustType::RawPtr { inner, .. }
            | RustType::Box { inner } => {
                if inner.is_sized() {
                    Some(8)
                } else {
                    Some(16)
                }
            }
            RustType::Function { .. } => Some(8),
            // Pin is repr(transparent): same size as inner
            RustType::Cell { inner }
            | RustType::RefCell { inner }
            | RustType::UnsafeCell { inner }
            | RustType::Pin { inner } => inner.size(),
            RustType::Array { element, len } => len
                .as_usize(&std::collections::HashMap::new())
                // A byte size that does not fit in `usize` is not representable,
                // so treat such an array as having no known size (`None`) rather
                // than overflowing the multiply. Under `overflow-checks` a plain
                // `s * len` would panic; in release it would wrap to a bogus
                // (tiny) size that `Memory::allocate_typed` would then trust.
                .and_then(|len| element.size().and_then(|s| s.checked_mul(len))),
            RustType::Tuple(elems) => {
                let mut size = 0usize;
                for elem in elems {
                    size = size.checked_add(elem.size()?)?;
                }
                Some(size)
            }
            RustType::Option { inner } => {
                // Option<T> has size of T + discriminant (usually 1)
                // But Option<&T> uses null pointer optimization
                if matches!(**inner, RustType::Reference { .. }) {
                    inner.size()
                } else {
                    inner.size().and_then(|s| s.checked_add(1))
                }
            }
            RustType::Result { ok, err } => {
                // Size is max(ok, err) + discriminant
                let ok_size = ok.size()?;
                let err_size = err.size()?;
                ok_size.max(err_size).checked_add(1)
            }
            RustType::Vec { .. } => Some(24), // ptr + len + cap
            // Unsized or unknown-size types
            RustType::Slice { .. }
            | RustType::Str
            | RustType::DynTrait { .. }
            | RustType::ImplTrait { .. }
            | RustType::Closure { .. }
            | RustType::Named { .. }
            | RustType::TypeParam(_)
            | RustType::TypeProjection { .. }
            | RustType::Infer => None,
        }
    }

    /// Check if type is sized (has known size at compile time)
    pub fn is_sized(&self) -> bool {
        self.size().is_some()
    }

    /// Check if type implements Copy
    pub fn is_copy(&self) -> bool {
        match self {
            RustType::Unit
            | RustType::Bool
            | RustType::Char
            | RustType::Uint(_)
            | RustType::Int(_)
            | RustType::Float(_)
            | RustType::RawPtr { .. }
            | RustType::Function { .. }
            | RustType::Never
            | RustType::Reference {
                mutability: Mutability::Shared,
                ..
            } => true,
            RustType::Array { element, .. } => element.is_copy(),
            RustType::Tuple(elems) => elems.iter().all(RustType::is_copy),
            // &mut T is not Copy, nor are heap allocations, unsized types, etc.
            RustType::Reference {
                mutability: Mutability::Mutable,
                ..
            }
            | RustType::Slice { .. }
            | RustType::Str
            | RustType::Named { .. }
            | RustType::TypeParam(_)
            | RustType::Box { .. }
            | RustType::Cell { .. }
            | RustType::RefCell { .. }
            | RustType::UnsafeCell { .. }
            | RustType::Atomic { .. }
            | RustType::Pin { .. }
            | RustType::Option { .. }
            | RustType::Result { .. }
            | RustType::Vec { .. }
            | RustType::DynTrait { .. }
            | RustType::ImplTrait { .. }
            | RustType::Closure { .. }
            | RustType::TypeProjection { .. }
            | RustType::Infer => false,
        }
    }

    /// Check if type is compatible (structurally equal) with another
    pub fn is_compatible(&self, other: &RustType) -> bool {
        match (self, other) {
            (RustType::Unit, RustType::Unit)
            | (RustType::Bool, RustType::Bool)
            | (RustType::Char, RustType::Char)
            | (RustType::Never, RustType::Never) => true,
            (RustType::Uint(a), RustType::Uint(b)) => a == b,
            (RustType::Int(a), RustType::Int(b)) => a == b,
            (RustType::Float(a), RustType::Float(b)) => a == b,
            (
                RustType::Reference {
                    lifetime: l1,
                    mutability: m1,
                    inner: i1,
                },
                RustType::Reference {
                    lifetime: l2,
                    mutability: m2,
                    inner: i2,
                },
            ) => l1 == l2 && m1 == m2 && i1.is_compatible(i2),
            (RustType::Atomic { inner: i1 }, RustType::Atomic { inner: i2 }) => {
                i1.is_compatible(i2)
            }
            (
                RustType::Array {
                    element: e1,
                    len: l1,
                },
                RustType::Array {
                    element: e2,
                    len: l2,
                },
            ) => l1 == l2 && e1.is_compatible(e2),
            (RustType::Tuple(e1), RustType::Tuple(e2)) => {
                e1.len() == e2.len() && e1.iter().zip(e2).all(|(a, b)| a.is_compatible(b))
            }
            (
                RustType::TypeProjection {
                    self_ty: s1,
                    trait_name: t1,
                    assoc_name: a1,
                    assoc_type_args: type_args1,
                    assoc_lifetime_args: lifetime_args1,
                    ..
                },
                RustType::TypeProjection {
                    self_ty: s2,
                    trait_name: t2,
                    assoc_name: a2,
                    assoc_type_args: type_args2,
                    assoc_lifetime_args: lifetime_args2,
                    ..
                },
            ) => {
                t1 == t2
                    && a1 == a2
                    && lifetime_args1 == lifetime_args2
                    && type_args1.len() == type_args2.len()
                    && type_args1
                        .iter()
                        .zip(type_args2.iter())
                        .all(|(left, right)| left.is_compatible(right))
                    && s1.is_compatible(s2)
            }
            _ => self == other,
        }
    }

    /// Check if this type has interior mutability (UnsafeCell-like)
    pub fn has_interior_mutability(&self) -> bool {
        match self {
            RustType::Atomic { .. } => true,
            // These would need to check for UnsafeCell wrapper
            RustType::Named { name, .. } => {
                matches!(
                    name.as_str(),
                    "Cell"
                        | "RefCell"
                        | "UnsafeCell"
                        | "OnceCell"
                        | "OnceLock"
                        | "Mutex"
                        | "RwLock"
                        | "AtomicBool"
                        | "AtomicI8"
                        | "AtomicI16"
                        | "AtomicI32"
                        | "AtomicI64"
                        | "AtomicU8"
                        | "AtomicU16"
                        | "AtomicU32"
                        | "AtomicU64"
                        | "AtomicUsize"
                        | "AtomicIsize"
                        | "AtomicPtr"
                )
            }
            _ => false,
        }
    }

    /// Check if type is Send (can be transferred between threads)
    pub fn is_send(&self) -> bool {
        match self {
            RustType::Unit
            | RustType::Bool
            | RustType::Char
            | RustType::Uint(_)
            | RustType::Int(_)
            | RustType::Float(_)
            | RustType::Atomic { .. }
            | RustType::Never => true,
            RustType::Reference { inner, .. } => inner.is_sync(),
            RustType::Array { element, .. } | RustType::Vec { element } => element.is_send(),
            RustType::Tuple(elems) => elems.iter().all(RustType::is_send),
            RustType::Box { inner }
            | RustType::Cell { inner }
            | RustType::RefCell { inner }
            | RustType::UnsafeCell { inner }
            | RustType::Pin { inner }
            | RustType::Option { inner } => inner.is_send(),
            RustType::Result { ok, err } => ok.is_send() && err.is_send(),
            // Raw pointers are not Send by default, nor are unsized types, etc.
            // TypeProjection is conservatively false until resolved.
            RustType::RawPtr { .. }
            | RustType::Slice { .. }
            | RustType::Str
            | RustType::Function { .. }
            | RustType::Named { .. }
            | RustType::TypeParam(_)
            | RustType::DynTrait { .. }
            | RustType::ImplTrait { .. }
            | RustType::Closure { .. }
            | RustType::TypeProjection { .. }
            | RustType::Infer => false,
        }
    }

    /// Check if type is Sync (can be shared between threads via &T)
    pub fn is_sync(&self) -> bool {
        match self {
            RustType::Unit
            | RustType::Bool
            | RustType::Char
            | RustType::Uint(_)
            | RustType::Int(_)
            | RustType::Float(_)
            | RustType::Atomic { .. }
            | RustType::Never => true,
            RustType::RawPtr { .. } => false,
            // Types with interior mutability need Sync wrapper
            t if t.has_interior_mutability() => false,
            RustType::Reference { inner, .. }
            | RustType::Box { inner }
            | RustType::Cell { inner }
            | RustType::RefCell { inner }
            | RustType::UnsafeCell { inner }
            | RustType::Pin { inner }
            | RustType::Option { inner } => inner.is_sync(),
            RustType::Array { element, .. } | RustType::Vec { element } => element.is_sync(),
            RustType::Tuple(elems) => elems.iter().all(RustType::is_sync),
            RustType::Result { ok, err } => ok.is_sync() && err.is_sync(),
            _ => false,
        }
    }

    /// Get the name of this type, if it's a named type
    ///
    /// Returns Some for Named types (structs, enums), DynTrait, ImplTrait, Box, etc.
    /// Returns None for primitive types (Int, Bool, etc.) and compound types.
    pub fn name(&self) -> Option<String> {
        match self {
            RustType::Named { name, .. } => Some(name.clone()),
            RustType::DynTrait {
                trait_name,
                auto_traits,
            } => {
                let mut names = vec![trait_name.clone()];
                names.extend(auto_traits.iter().cloned());
                Some(format!("dyn {}", names.join(" + ")))
            }
            RustType::ImplTrait { traits, .. } => Some(format!("impl {}", traits.join(" + "))),
            RustType::Box { inner } => Some(format!(
                "Box<{}>",
                inner.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::Cell { inner } => Some(format!(
                "Cell<{}>",
                inner.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::RefCell { inner } => Some(format!(
                "RefCell<{}>",
                inner.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::UnsafeCell { inner } => Some(format!(
                "UnsafeCell<{}>",
                inner.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::Pin { inner } => Some(format!(
                "Pin<{}>",
                inner.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::Vec { element } => Some(format!(
                "Vec<{}>",
                element.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::Option { inner } => Some(format!(
                "Option<{}>",
                inner.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::Result { ok, err } => Some(format!(
                "Result<{}, {}>",
                ok.name().unwrap_or_else(|| "_".to_string()),
                err.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::Atomic { inner } => Some(format!(
                "Atomic<{}>",
                inner.name().unwrap_or_else(|| "_".to_string())
            )),
            RustType::TypeProjection {
                self_ty,
                trait_name,
                assoc_name,
                assoc_type_args,
                assoc_lifetime_args,
                ..
            } => Some(format!(
                "<{} as {}>::{}{}",
                self_ty.name().unwrap_or_else(|| "_".to_string()),
                trait_name,
                assoc_name,
                format_projection_args(assoc_type_args, assoc_lifetime_args)
            )),
            _ => None,
        }
    }
}

fn format_projection_args(type_args: &[RustType], lifetime_args: &[Lifetime]) -> String {
    if type_args.is_empty() && lifetime_args.is_empty() {
        return String::new();
    }

    let mut args = lifetime_args
        .iter()
        .map(format_lifetime_arg)
        .collect::<Vec<_>>();
    args.extend(
        type_args
            .iter()
            .map(|ty| ty.name().unwrap_or_else(|| "_".to_string())),
    );
    format!("<{}>", args.join(", "))
}

fn format_lifetime_arg(lifetime: &Lifetime) -> String {
    match lifetime {
        Lifetime::Static => "'static".to_string(),
        Lifetime::Named(name) => format!("'{name}"),
        Lifetime::Anonymous(_) | Lifetime::Existential(_) => "'_".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::super::*;

    #[test]
    fn test_primitive_sizes() {
        assert_eq!(RustType::Unit.size(), Some(0));
        assert_eq!(RustType::Bool.size(), Some(1));
        assert_eq!(RustType::Char.size(), Some(4));
        assert_eq!(RustType::Uint(UintType::U8).size(), Some(1));
        assert_eq!(RustType::Uint(UintType::U64).size(), Some(8));
        assert_eq!(RustType::Int(IntType::I32).size(), Some(4));
        assert_eq!(RustType::Float(FloatType::F64).size(), Some(8));
    }

    #[test]
    fn test_array_size_overflow_returns_none_not_panic() {
        // Regression: `[u64; N]` with N so large that `8 * N` overflows usize
        // must not panic (overflow-checks) or silently wrap (release). Such a
        // type has no representable byte size, so `size()` returns `None`.
        let huge = RustType::Array {
            element: Box::new(RustType::Uint(UintType::U64)),
            len: ConstGenericArg::usize(usize::MAX / 2),
        };
        assert_eq!(
            huge.size(),
            None,
            "an array whose byte size overflows usize has no representable size"
        );

        // A tuple containing such an unrepresentable array must also be None,
        // not overflow the running `size` accumulator.
        let tuple = RustType::Tuple(vec![RustType::Bool, huge.clone()]);
        assert_eq!(tuple.size(), None);

        // Normal arrays still report their exact size.
        let ok = RustType::Array {
            element: Box::new(RustType::Uint(UintType::U64)),
            len: ConstGenericArg::usize(4),
        };
        assert_eq!(ok.size(), Some(32));
    }

    #[test]
    fn test_copy_types() {
        assert!(RustType::Bool.is_copy());
        assert!(RustType::Uint(UintType::U32).is_copy());
        assert!(RustType::Int(IntType::I64).is_copy());

        let shared_ref = RustType::Reference {
            lifetime: Lifetime::Static,
            mutability: Mutability::Shared,
            inner: Box::new(RustType::Bool),
        };
        assert!(shared_ref.is_copy());

        let mut_ref = RustType::Reference {
            lifetime: Lifetime::Static,
            mutability: Mutability::Mutable,
            inner: Box::new(RustType::Bool),
        };
        assert!(!mut_ref.is_copy());
    }

    #[test]
    fn test_closure_type() {
        let closure_ty = RustType::Closure {
            params: vec![RustType::Uint(UintType::U32)],
            ret: Box::new(RustType::Uint(UintType::U64)),
            captures: vec![(
                "x".to_string(),
                RustType::Int(IntType::I32),
                Mutability::Shared,
            )],
            kind: ClosureKind::Fn,
        };
        // Closures are not Copy
        assert!(!closure_ty.is_copy());
        // Closures have unknown size (environment-dependent)
        assert_eq!(
            closure_ty.size(),
            None,
            "closures have unknown (environment-dependent) size"
        );
    }

    #[test]
    fn test_type_projection_basic() {
        // <Vec<i32> as IntoIterator>::Item
        let projection = RustType::TypeProjection {
            self_ty: Box::new(RustType::Vec {
                element: Box::new(RustType::Int(IntType::I32)),
            }),
            trait_name: "IntoIterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };

        // Type projections have unknown size until resolved
        assert_eq!(
            projection.size(),
            None,
            "type projections have unknown size until resolved"
        );

        // Type projections are not Copy (unknown until resolved)
        assert!(!projection.is_copy());

        // Type projections are not Send/Sync until resolved
        assert!(!projection.is_send());
        assert!(!projection.is_sync());
    }

    #[test]
    fn test_type_projection_name() {
        let projection = RustType::TypeProjection {
            self_ty: Box::new(RustType::Named {
                name: "MyType".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            }),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };

        assert_eq!(
            projection.name(),
            Some("<MyType as Iterator>::Item".to_string())
        );
    }

    #[test]
    fn test_type_projection_compatibility() {
        // Use primitive types for self_ty since is_compatible doesn't handle Named yet
        let proj1 = RustType::TypeProjection {
            self_ty: Box::new(RustType::Int(IntType::I32)),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };

        let proj2 = RustType::TypeProjection {
            self_ty: Box::new(RustType::Int(IntType::I32)),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };

        // Same projections should be compatible
        assert!(proj1.is_compatible(&proj2));

        // Different trait name → not compatible
        let proj_diff_trait = RustType::TypeProjection {
            self_ty: Box::new(RustType::Int(IntType::I32)),
            trait_name: "IntoIterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };
        assert!(!proj1.is_compatible(&proj_diff_trait));

        // Different assoc name → not compatible
        let proj_diff_assoc = RustType::TypeProjection {
            self_ty: Box::new(RustType::Int(IntType::I32)),
            trait_name: "Iterator".to_string(),
            assoc_name: "Output".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };
        assert!(!proj1.is_compatible(&proj_diff_assoc));

        // Different self_ty → not compatible
        let proj_diff_self = RustType::TypeProjection {
            self_ty: Box::new(RustType::Int(IntType::I64)),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };
        assert!(!proj1.is_compatible(&proj_diff_self));
    }

    #[test]
    fn test_type_projection_serialization() {
        let projection = RustType::TypeProjection {
            self_ty: Box::new(RustType::Int(IntType::I32)),
            trait_name: "Iterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };

        // Serialize to JSON
        let json = serde_json::to_string(&projection).expect("serialize");
        assert!(json.contains("TypeProjection"));
        assert!(json.contains("Iterator"));
        assert!(json.contains("Item"));

        // Deserialize back
        let deserialized: RustType = serde_json::from_str(&json).expect("deserialize");
        assert!(projection.is_compatible(&deserialized));
    }

    // ---- has_interior_mutability ----

    #[test]
    fn test_has_interior_mutability_atomic_variant_is_true() {
        let atomic = RustType::Atomic {
            inner: Box::new(RustType::Uint(UintType::U32)),
        };
        assert!(atomic.has_interior_mutability());
    }

    #[test]
    fn test_has_interior_mutability_named_cell_like_is_true() {
        for name in [
            "Cell",
            "RefCell",
            "UnsafeCell",
            "OnceCell",
            "OnceLock",
            "Mutex",
            "RwLock",
            "AtomicBool",
            "AtomicI32",
            "AtomicUsize",
            "AtomicPtr",
        ] {
            let named = RustType::Named {
                name: name.to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            };
            assert!(
                named.has_interior_mutability(),
                "{name} should have interior mutability"
            );
        }
    }

    #[test]
    fn test_has_interior_mutability_plain_named_is_false() {
        let named = RustType::Named {
            name: "MyStruct".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        };
        assert!(!named.has_interior_mutability());
        assert!(!RustType::Bool.has_interior_mutability());
        assert!(!RustType::Uint(UintType::U32).has_interior_mutability());
    }

    // ---- is_send / is_sync: primitives ----

    #[test]
    fn test_send_sync_primitives_are_both() {
        for ty in [
            RustType::Unit,
            RustType::Bool,
            RustType::Char,
            RustType::Uint(UintType::U32),
            RustType::Int(IntType::I64),
            RustType::Float(FloatType::F64),
            RustType::Never,
        ] {
            assert!(ty.is_send(), "{ty:?} should be Send");
            assert!(ty.is_sync(), "{ty:?} should be Sync");
        }
    }

    // ---- &T: Send iff T: Sync ----

    #[test]
    fn test_shared_ref_send_iff_inner_sync() {
        // &u32: inner u32 is Sync, so &u32 is Send.
        let ref_to_sync = RustType::Reference {
            lifetime: Lifetime::Static,
            mutability: Mutability::Shared,
            inner: Box::new(RustType::Uint(UintType::U32)),
        };
        assert!(ref_to_sync.is_send(), "&u32 is Send because u32 is Sync");
        assert!(ref_to_sync.is_sync(), "&u32 is Sync because u32 is Sync");

        // &*const T: inner raw pointer is NOT Sync, so the reference is NOT Send.
        let ref_to_rawptr = RustType::Reference {
            lifetime: Lifetime::Static,
            mutability: Mutability::Shared,
            inner: Box::new(RustType::RawPtr {
                inner: Box::new(RustType::Uint(UintType::U32)),
                mutability: Mutability::Shared,
            }),
        };
        assert!(
            !ref_to_rawptr.is_send(),
            "&*const u32 is not Send because *const u32 is not Sync"
        );
    }

    // ---- raw pointers: neither Send nor Sync ----

    #[test]
    fn test_raw_pointer_is_neither_send_nor_sync() {
        let raw = RustType::RawPtr {
            inner: Box::new(RustType::Uint(UintType::U32)),
            mutability: Mutability::Mutable,
        };
        assert!(!raw.is_send(), "raw pointers are not Send");
        assert!(!raw.is_sync(), "raw pointers are not Sync");
    }

    // ---- interior-mutability Named types are not Sync ----

    #[test]
    fn test_interior_mutability_named_types_are_not_sync() {
        for name in ["Cell", "RefCell", "Mutex", "AtomicBool", "AtomicU64"] {
            let named = RustType::Named {
                name: name.to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            };
            assert!(!named.is_sync(), "{name} is not Sync (interior mutability)");
        }
    }

    #[test]
    fn test_atomic_variant_is_send_and_sync() {
        // The dedicated Atomic variant short-circuits to Send + Sync
        // (it represents an already-synchronized atomic scalar).
        let atomic = RustType::Atomic {
            inner: Box::new(RustType::Uint(UintType::U32)),
        };
        assert!(atomic.is_send(), "Atomic<u32> is Send");
        assert!(atomic.is_sync(), "Atomic<u32> is Sync");
    }

    // ---- recursion through Tuple / Result / Option / Vec ----

    #[test]
    fn test_send_sync_recurse_through_tuple() {
        let ok_tuple = RustType::Tuple(vec![RustType::Bool, RustType::Uint(UintType::U8)]);
        assert!(ok_tuple.is_send());
        assert!(ok_tuple.is_sync());

        // A raw pointer element poisons both Send and Sync.
        let bad_tuple = RustType::Tuple(vec![
            RustType::Bool,
            RustType::RawPtr {
                inner: Box::new(RustType::Unit),
                mutability: Mutability::Shared,
            },
        ]);
        assert!(!bad_tuple.is_send());
        assert!(!bad_tuple.is_sync());
    }

    #[test]
    fn test_send_sync_recurse_through_option_and_vec() {
        let opt = RustType::Option {
            inner: Box::new(RustType::Bool),
        };
        assert!(opt.is_send());
        assert!(opt.is_sync());

        let vec_ty = RustType::Vec {
            element: Box::new(RustType::Uint(UintType::U64)),
        };
        assert!(vec_ty.is_send());
        assert!(vec_ty.is_sync());

        // Vec of raw pointers is neither.
        let vec_raw = RustType::Vec {
            element: Box::new(RustType::RawPtr {
                inner: Box::new(RustType::Unit),
                mutability: Mutability::Shared,
            }),
        };
        assert!(!vec_raw.is_send());
        assert!(!vec_raw.is_sync());
    }

    #[test]
    fn test_send_sync_recurse_through_result() {
        let ok_result = RustType::Result {
            ok: Box::new(RustType::Bool),
            err: Box::new(RustType::Uint(UintType::U32)),
        };
        assert!(ok_result.is_send());
        assert!(ok_result.is_sync());

        // A raw pointer in either arm poisons Send and Sync.
        let bad_ok = RustType::Result {
            ok: Box::new(RustType::RawPtr {
                inner: Box::new(RustType::Unit),
                mutability: Mutability::Shared,
            }),
            err: Box::new(RustType::Bool),
        };
        assert!(!bad_ok.is_send());
        assert!(!bad_ok.is_sync());

        let bad_err = RustType::Result {
            ok: Box::new(RustType::Bool),
            err: Box::new(RustType::RawPtr {
                inner: Box::new(RustType::Unit),
                mutability: Mutability::Shared,
            }),
        };
        assert!(!bad_err.is_send());
        assert!(!bad_err.is_sync());
    }

    #[test]
    fn test_pin_type_properties() {
        let pin_box = RustType::Pin {
            inner: Box::new(RustType::Box {
                inner: Box::new(RustType::Uint(UintType::U32)),
            }),
        };
        assert_eq!(pin_box.size(), Some(8), "Pin<Box<T>> is pointer-sized");
        assert!(!pin_box.is_copy(), "Pin<Box<T>> is not Copy");
        assert!(pin_box.is_send(), "Pin<Box<u32>> is Send");
        assert!(pin_box.is_sync(), "Pin<Box<u32>> is Sync");

        let pin_named = RustType::Pin {
            inner: Box::new(RustType::Box {
                inner: Box::new(RustType::Named {
                    name: "F".to_string(),
                    type_args: vec![],
                    lifetime_args: vec![],
                    const_args: vec![],
                }),
            }),
        };
        assert_eq!(pin_named.name(), Some("Pin<Box<F>>".to_string()));
    }
}
