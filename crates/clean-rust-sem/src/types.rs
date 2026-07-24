// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust Type System Formalization
//!
//! This module defines the Rust type system as it relates to
//! ownership and borrowing semantics.
//!
//! ## Type Categories
//!
//! - **Primitive Types**: bool, integers, floats, char
//! - **Compound Types**: tuples, arrays, structs, enums
//! - **Reference Types**: &T, &mut T with lifetimes
//! - **Pointer Types**: *const T, *mut T
//! - **Function Types**: fn(A) -> B
//! - **Trait Objects**: dyn Trait
//!
//! ## Ownership Properties
//!
//! Types have several ownership-related properties:
//!
//! - **Copy**: Type can be bitwise copied (no ownership transfer)
//! - **Clone**: Type can be explicitly cloned
//! - **Drop**: Type has custom destructor
//! - **Send**: Type can be sent between threads
//! - **Sync**: Type can be shared between threads via references

mod closures;
mod const_generics;
mod definitions;
mod gat;
mod primitives;
mod properties;
mod substitution;
mod vtable;

pub use closures::ClosureKind;
pub use const_generics::{
    dependent_const_eval, validate_const_generic_bounds, ConstGenericBound, ConstGenericEval,
    ConstGenericUnifier,
};
pub use definitions::{
    EnumDef, EnumVariant, FunctionSignature, ReceiverMode, StructDef, StructField, Visibility,
};
pub use gat::{resolve_gat, validate_gat_bounds, GatDef, GatProjection, GatSubstitution};
pub use primitives::{FloatType, IntType, UintType};
pub use vtable::{TypeContext, VTable};

use serde::{Deserialize, Serialize};

/// Mutability qualifier for references and pointers
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Mutability {
    /// Shared/immutable access
    Shared,
    /// Exclusive/mutable access
    Mutable,
}

/// Lifetime in the Rust type system
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Lifetime {
    /// Static lifetime (lives for entire program)
    Static,
    /// Named lifetime parameter (e.g., 'a)
    Named(String),
    /// Anonymous/elided lifetime
    Anonymous(u32),
    /// Existential lifetime (for type inference)
    Existential(u32),
}

impl Lifetime {
    /// Check if this lifetime outlives another
    pub fn outlives(&self, other: &Lifetime) -> bool {
        match (self, other) {
            (Lifetime::Static, _) => true,
            (Lifetime::Named(a), Lifetime::Named(b)) => a == b,
            // Conservative: unknown lifetimes don't outlive each other
            (_, Lifetime::Static)
            | (Lifetime::Named(_), _)
            | (_, Lifetime::Named(_))
            | (Lifetime::Anonymous(_), _)
            | (Lifetime::Existential(_), _) => false,
        }
    }
}

/// Type variable for generic types
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct TypeVar {
    pub id: u32,
    pub name: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConstGenericValue {
    Usize(usize),
    Bool(bool),
    Char(char),
    I32(i32),
    Unknown,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ConstGenericArg {
    Value(ConstGenericValue),
    Param(String),
    Add(Box<ConstGenericArg>, Box<ConstGenericArg>),
    Sub(Box<ConstGenericArg>, Box<ConstGenericArg>),
    Mul(Box<ConstGenericArg>, Box<ConstGenericArg>),
    Div(Box<ConstGenericArg>, Box<ConstGenericArg>),
    Rem(Box<ConstGenericArg>, Box<ConstGenericArg>),
    Neg(Box<ConstGenericArg>),
}

impl ConstGenericArg {
    #[must_use]
    pub const fn usize(value: usize) -> Self {
        Self::Value(ConstGenericValue::Usize(value))
    }

    #[must_use]
    pub fn resolve(
        &self,
        subst: &std::collections::HashMap<String, ConstGenericValue>,
    ) -> ConstGenericValue {
        ConstGenericEval::eval(self, subst)
    }

    #[must_use]
    pub fn as_usize(
        &self,
        subst: &std::collections::HashMap<String, ConstGenericValue>,
    ) -> Option<usize> {
        match self.resolve(subst) {
            ConstGenericValue::Usize(value) => Some(value),
            ConstGenericValue::Bool(_)
            | ConstGenericValue::Char(_)
            | ConstGenericValue::I32(_)
            | ConstGenericValue::Unknown => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct ConstParamDef {
    pub name: String,
    pub ty: RustType,
}

/// Type parameter definition from a generic declaration
///
/// Represents `T: Clone + Debug` in `fn foo<T: Clone + Debug>()`.
/// Lifetime parameters are stored separately as strings.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct TypeParamDef {
    #[serde(default)]
    pub id: u32,
    pub name: String,
    pub bounds: Vec<String>,
}

/// Rust type representation
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum RustType {
    /// Unit type ()
    Unit,

    /// Boolean
    Bool,

    /// Character (Unicode scalar)
    Char,

    /// Unsigned integer
    Uint(UintType),

    /// Signed integer
    Int(IntType),

    /// Floating point
    Float(FloatType),

    /// Reference with lifetime
    Reference {
        lifetime: Lifetime,
        mutability: Mutability,
        inner: Box<RustType>,
    },

    /// Raw pointer
    RawPtr {
        mutability: Mutability,
        inner: Box<RustType>,
    },

    /// Atomic scalar or pointer with interior mutability
    Atomic { inner: Box<RustType> },

    /// Fixed-size array [T; N]
    Array {
        element: Box<RustType>,
        len: ConstGenericArg,
    },

    /// Slice type `[T]`
    Slice { elem: Box<RustType> },

    /// String slice str
    Str,

    /// Tuple (T1, T2, ...)
    Tuple(Vec<RustType>),

    /// Function type fn(Args) -> Ret
    Function {
        params: Vec<RustType>,
        ret: Box<RustType>,
    },

    /// Named type (struct, enum, etc.)
    Named {
        name: String,
        /// Generic type arguments
        type_args: Vec<RustType>,
        /// Generic lifetime arguments
        lifetime_args: Vec<Lifetime>,
        /// Generic const arguments
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_args: Vec<ConstGenericArg>,
    },

    /// Type parameter (generic T)
    TypeParam(TypeVar),

    /// The "never" type !
    Never,

    /// `Box<T>` - owned heap allocation
    Box { inner: Box<RustType> },

    /// `Cell<T>` - copy-based interior mutability
    Cell { inner: Box<RustType> },

    /// `RefCell<T>` - dynamically checked interior mutability
    RefCell { inner: Box<RustType> },

    /// `UnsafeCell<T>` - primitive interior mutability escape hatch
    UnsafeCell { inner: Box<RustType> },

    /// `Pin<P>` - pinned pointer wrapper
    ///
    /// `Pin<P>` is a `#[repr(transparent)]` wrapper around a pointer type P
    /// that prevents the pointed-to value from being moved. In the verification
    /// model, Pin is semantically transparent (same layout as inner).
    /// Primary use: `Pin<Box<dyn Future<Output = T>>>` in async trait returns.
    Pin { inner: Box<RustType> },

    /// `Option<T>`
    Option { inner: Box<RustType> },

    /// Result<T, E>
    Result {
        ok: Box<RustType>,
        err: Box<RustType>,
    },

    /// `Vec<T>`
    Vec { element: Box<RustType> },

    /// Dynamic trait object dyn Trait
    DynTrait {
        trait_name: String,
        auto_traits: Vec<String>,
    },

    /// Impl trait (impl Trait)
    ImplTrait { traits: Vec<String> },

    /// Closure type (with captured environment)
    ///
    /// Closures are anonymous functions that can capture their environment.
    /// The `kind` field determines which Fn traits the closure implements.
    Closure {
        /// Parameter types
        params: Vec<RustType>,
        /// Return type (inferred from body or explicitly annotated)
        ret: Box<RustType>,
        /// Captured variables: (name, type, capture mode)
        captures: Vec<(String, RustType, Mutability)>,
        /// Closure kind: Fn, FnMut, or FnOnce
        kind: ClosureKind,
    },

    /// Inferred type (placeholder for unresolved type inference)
    ///
    /// Used for closure parameters without type annotations (e.g., `|x| x + 1`).
    /// At runtime, the actual type is determined by the value passed as an argument.
    Infer,

    /// Type projection: `<T as Trait>::Assoc`
    ///
    /// Represents an associated type projection. For example,
    /// `<Vec<i32> as IntoIterator>::Item` projects the `Item` associated
    /// type from the `IntoIterator` impl for `Vec<i32>`. Generic associated
    /// types store their instantiation arguments in `assoc_type_args` and
    /// `assoc_lifetime_args`.
    ///
    /// Type projections must be resolved (normalized) before they can be
    /// used in type checking. See `ExecContext::resolve_type_projection`.
    ///
    /// Reference: Rust Reference, "Paths in types"
    /// <https://doc.rust-lang.org/reference/paths.html#paths-in-types>
    TypeProjection {
        /// The Self type (e.g., `Vec<i32>` in `<Vec<i32> as IntoIterator>::Item`)
        self_ty: Box<RustType>,
        /// The trait name (e.g., `IntoIterator`)
        trait_name: String,
        /// The associated type name (e.g., `Item`)
        assoc_name: String,
        /// Generic type arguments applied to the associated type (e.g., `U`
        /// in `<T as Trait>::Assoc<U>`).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        assoc_type_args: Vec<RustType>,
        /// Generic lifetime arguments applied to the associated type (e.g.,
        /// `'a` in `<T as Trait>::Assoc<'a>`).
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        assoc_lifetime_args: Vec<Lifetime>,
        /// Generic const arguments applied to the associated type
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_args: Vec<ConstGenericArg>,
    },
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lifetime_outlives() {
        let static_lt = Lifetime::Static;
        let named_a = Lifetime::Named("a".to_string());
        let named_b = Lifetime::Named("b".to_string());

        assert!(static_lt.outlives(&named_a));
        assert!(!named_a.outlives(&static_lt));
        assert!(named_a.outlives(&named_a));
        assert!(!named_a.outlives(&named_b));
    }
}
