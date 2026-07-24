// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rust statement execution semantics (let bindings, items, expression stmts).

// Re-export from expr.rs where Stmt is defined
pub use crate::expr::{Item, Stmt};
// Re-export pattern matching from extracted module
pub use crate::pattern_match::{match_pattern, match_pattern_typed, PatternBindings};

use crate::expr::Expr;
use crate::memory::Memory;
use crate::ownership::OwnershipState;
use crate::stack::Stack;
use crate::trait_defaults::DefaultMethodBody;
use crate::types::{
    resolve_gat as normalize_gat_projection, ConstParamDef, FunctionSignature, GatDef,
    GatProjection, GatSubstitution, Lifetime, RustType, TypeParamDef,
};
use crate::values::Value;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;

/// Execution context for statement evaluation
#[derive(Debug)]
pub struct ExecContext {
    /// Memory model
    pub memory: Memory,
    /// Call stack
    pub stack: Stack,
    /// Ownership state
    pub ownership: OwnershipState,
    /// Named functions
    pub functions: HashMap<String, FunctionDef>,
    /// Additional generic type parameters inherited from surrounding item
    /// context (for example, `impl<T> Type<T> { ... }` on an associated
    /// function that has no method-local generics of its own).
    pub function_type_param_contexts: HashMap<String, Vec<TypeParamDef>>,
    /// Named types (structs, enums)
    pub types: HashMap<String, TypeDef>,
    /// Drop implementations: type_name -> drop function name
    pub drop_impls: HashMap<String, String>,
    /// Trait implementations keyed by self type, then trait name.
    ///
    /// Stores which types implement which traits, enabling method resolution
    /// for trait methods on concrete types.
    pub trait_impls: HashMap<String, HashMap<String, TraitImplInfo>>,
    /// Cached trait method dispatch keyed by self type, then method, then trait.
    ///
    /// This avoids rescanning every trait impl for a type on each method lookup.
    trait_method_impls: HashMap<String, HashMap<String, HashMap<String, String>>>,
    /// Trait definitions: trait_name -> trait definition
    ///
    /// Stores the trait method signatures and associated types for validation
    /// during static dispatch and type projection resolution.
    pub trait_defs: HashMap<String, TraitDef>,
    /// Whether we are currently executing in an unsafe context
    ///
    /// This is true when:
    /// - Inside an `unsafe { }` block
    /// - Inside an `unsafe fn` body
    ///
    /// Used to validate that unsafe operations (raw pointer deref,
    /// calling unsafe functions) are only performed in unsafe context.
    pub in_unsafe: bool,
}

/// Information about a trait implementation
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitImplInfo {
    /// The trait being implemented
    pub trait_name: String,
    /// The implementing type (as a RustType for full type info)
    pub self_ty: RustType,
    /// Methods provided by this impl (method_name -> implementing function name)
    pub methods: HashMap<String, String>,
    /// Associated type definitions provided by this impl
    ///
    /// For example, `impl Iterator for Counter { type Item = i32; }`
    /// would have `associated_types = { "Item" -> AssociatedTypeValue { ty:
    /// RustType::Int(I32), .. } }`.
    pub associated_types: HashMap<String, AssociatedTypeValue>,
}

/// Generic parameter supported on associated types.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum GenericParam {
    /// Lifetime parameter (e.g., `'a`)
    Lifetime(String),
    /// Type parameter (e.g., `T: Clone`)
    Type(TypeParamDef),
}

impl GenericParam {
    #[must_use]
    pub fn lifetime(name: impl Into<String>) -> Self {
        Self::Lifetime(name.into())
    }

    #[must_use]
    pub fn type_param(type_param: TypeParamDef) -> Self {
        Self::Type(type_param)
    }

    #[must_use]
    pub fn as_type_param(&self) -> Option<&TypeParamDef> {
        match self {
            Self::Type(type_param) => Some(type_param),
            Self::Lifetime(_) => None,
        }
    }

    #[must_use]
    pub fn as_lifetime_name(&self) -> Option<&str> {
        match self {
            Self::Lifetime(name) => Some(name.as_str()),
            Self::Type(_) => None,
        }
    }
}

/// Where-clause predicate supported on associated types and GAT impls.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub enum WherePredicate {
    /// Type predicate like `Self: 'a + Clone`
    Type { ty: RustType, bounds: Vec<String> },
    /// Lifetime predicate like `'a: 'b`
    Lifetime {
        lifetime: String,
        bounds: Vec<String>,
    },
}

/// Complete trait definition including methods, associated types, and default bodies
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TraitDef {
    /// Trait name
    pub name: String,
    /// Supertrait names (e.g., `trait Foo: Bar + Baz` → `["Bar", "Baz"]`)
    #[serde(default)]
    pub supertraits: Vec<String>,
    /// Method signatures
    pub methods: Vec<FunctionSignature>,
    /// Associated types with their bounds
    pub associated_types: Vec<AssociatedTypeDef>,
    /// Associated constants (e.g., `const MAX: u32;`)
    #[serde(default)]
    pub associated_constants: Vec<AssociatedConstDef>,
    /// Default method bodies (method_name -> body)
    #[serde(default)]
    pub default_bodies: HashMap<String, DefaultMethodBody>,
    /// Generic type parameters (e.g., `trait From<T>` → `[TypeParamDef { name: "T", .. }]`)
    #[serde(default)]
    pub type_params: Vec<TypeParamDef>,
}

impl TraitDef {
    /// Create a new trait definition with only methods (no associated types)
    #[must_use]
    pub fn new(name: String, methods: Vec<FunctionSignature>) -> Self {
        Self {
            name,
            supertraits: Vec::new(),
            methods,
            associated_types: Vec::new(),
            associated_constants: Vec::new(),
            default_bodies: HashMap::new(),
            type_params: Vec::new(),
        }
    }

    /// Create a new trait definition with methods and associated types
    #[must_use]
    pub fn with_associated_types(
        name: String,
        methods: Vec<FunctionSignature>,
        associated_types: Vec<AssociatedTypeDef>,
    ) -> Self {
        let mut def = Self::new(name, methods);
        def.associated_types = associated_types;
        def
    }
}

/// Associated type definition in a trait
///
/// Represents an associated type declaration like `type Item: Clone;`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssociatedTypeDef {
    /// Associated type name (e.g., "Item")
    pub name: String,
    /// Associated generic parameters (e.g., `['a, T]` for `type Item<'a, T>;`)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub generic_params: Vec<GenericParam>,
    /// Trait bounds (e.g., `["Clone", "Debug"]` for `type Item: Clone + Debug`)
    pub bounds: Vec<String>,
    /// Explicit where-clause predicates (e.g., `Self: 'a`)
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub where_clause: Vec<WherePredicate>,
    /// Default type if provided (e.g., `type Item = ();`)
    pub default: Option<RustType>,
}

impl AssociatedTypeDef {
    /// Create a new associated type definition without bounds or default
    #[must_use]
    pub fn new(name: String, generic_params: Vec<GenericParam>) -> Self {
        Self {
            name,
            generic_params,
            bounds: Vec::new(),
            where_clause: Vec::new(),
            default: None,
        }
    }

    /// Create a new associated type definition with bounds
    #[must_use]
    pub fn with_bounds(
        name: String,
        generic_params: Vec<GenericParam>,
        bounds: Vec<String>,
    ) -> Self {
        Self {
            name,
            generic_params,
            bounds,
            where_clause: Vec::new(),
            default: None,
        }
    }

    /// Create a new associated type definition with a default type
    #[must_use]
    pub fn with_default(
        name: String,
        generic_params: Vec<GenericParam>,
        default: RustType,
    ) -> Self {
        let mut def = Self::new(name, generic_params);
        def.default = Some(default);
        def
    }

    /// Create a new associated type definition with bounds and a default type
    #[must_use]
    pub fn with_bounds_and_default(
        name: String,
        generic_params: Vec<GenericParam>,
        bounds: Vec<String>,
        default: RustType,
    ) -> Self {
        let mut def = Self::with_bounds(name, generic_params, bounds);
        def.default = Some(default);
        def
    }

    /// Attach a where-clause to the associated type definition.
    #[must_use]
    pub fn with_where_clause(mut self, where_clause: Vec<WherePredicate>) -> Self {
        self.where_clause = where_clause;
        self
    }
}

/// Concrete associated type definition stored on a trait impl.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssociatedTypeValue {
    /// Associated generic parameters declared by the impl item.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub generic_params: Vec<GenericParam>,
    /// Explicit where-clause predicates declared by the impl item.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub where_clause: Vec<WherePredicate>,
    /// The concrete type body provided by the impl.
    pub ty: RustType,
}

impl TraitImplInfo {
    #[must_use]
    pub(crate) fn resolve_associated_type(
        &self,
        concrete_self_ty: &RustType,
        assoc_name: &str,
        assoc_type_args: &[RustType],
        assoc_lifetime_args: &[Lifetime],
    ) -> Option<RustType> {
        normalize_gat_projection(
            &GatProjection::new(
                concrete_self_ty.clone(),
                self.trait_name.clone(),
                assoc_name.to_string(),
                assoc_type_args.to_vec(),
                assoc_lifetime_args.to_vec(),
            ),
            self,
        )
    }
}

/// Associated constant definition in a trait
///
/// Represents an associated constant declaration like `const MAX: u32 = 100;`
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AssociatedConstDef {
    /// Constant name (e.g., "MAX")
    pub name: String,
    /// Constant type
    pub ty: RustType,
    /// Default value if provided (e.g., `const MAX: u32 = 100;`)
    pub has_default: bool,
}

/// Function definition
#[derive(Debug, Clone)]
pub struct FunctionDef {
    pub name: String,
    pub params: Vec<(String, RustType)>,
    pub ret_ty: RustType,
    pub body: Expr,
    /// Whether this function is marked `unsafe fn`
    pub is_unsafe: bool,
    /// Whether this function is marked `async fn`
    pub is_async: bool,
    /// Generic type parameters (empty for non-generic functions)
    pub type_params: Vec<TypeParamDef>,
}

/// Type definition (struct, enum, or union)
#[derive(Debug, Clone)]
pub enum TypeDef {
    Struct {
        name: String,
        fields: Vec<(String, RustType)>,
        /// Generic type parameters (empty for non-generic structs)
        type_params: Vec<TypeParamDef>,
        const_params: Vec<ConstParamDef>,
    },
    Enum {
        name: String,
        variants: Vec<EnumVariantDef>,
        /// Generic type parameters (empty for non-generic enums)
        type_params: Vec<TypeParamDef>,
        const_params: Vec<ConstParamDef>,
    },
    /// Rust union type - all fields share the same memory
    ///
    /// Union field access is unsafe because the compiler cannot
    /// track which field was most recently written.
    Union {
        name: String,
        /// Fields share the same memory location
        fields: Vec<(String, RustType)>,
        const_params: Vec<ConstParamDef>,
    },
}

/// Enum variant definition
#[derive(Debug, Clone)]
pub struct EnumVariantDef {
    pub name: String,
    pub payload: EnumVariantType,
    pub discriminant: Option<i128>,
}

/// Enum variant payload type
#[derive(Debug, Clone)]
pub enum EnumVariantType {
    Unit,
    Tuple(Vec<RustType>),
    Struct(Vec<(String, RustType)>),
}

impl ExecContext {
    /// Create a new execution context
    #[must_use]
    pub fn new() -> Self {
        Self {
            memory: Memory::new(),
            stack: Stack::new(),
            ownership: OwnershipState::new(),
            functions: HashMap::new(),
            function_type_param_contexts: HashMap::new(),
            types: HashMap::new(),
            drop_impls: HashMap::new(),
            trait_impls: HashMap::new(),
            trait_method_impls: HashMap::new(),
            trait_defs: HashMap::new(),
            in_unsafe: false,
        }
    }

    /// Enter unsafe context (for unsafe blocks or unsafe fn calls)
    #[must_use]
    pub fn enter_unsafe(&mut self) -> bool {
        let was_unsafe = self.in_unsafe;
        self.in_unsafe = true;
        was_unsafe
    }

    /// Exit unsafe context, restoring previous state
    pub fn exit_unsafe(&mut self, previous: bool) {
        self.in_unsafe = previous;
    }

    /// Check if we're in an unsafe context
    #[must_use]
    pub fn is_unsafe(&self) -> bool {
        self.in_unsafe
    }

    /// Require unsafe context, returning error if not
    pub fn require_unsafe(&self, operation: &str) -> Result<(), crate::error::RustSemError> {
        if self.in_unsafe {
            Ok(())
        } else {
            Err(crate::error::RustSemError::UnsafeRequired {
                operation: operation.to_string(),
            })
        }
    }

    /// Register a function
    pub fn register_function(&mut self, def: FunctionDef) {
        self.functions.insert(def.name.clone(), def);
    }

    /// Register inherited generic parameters for a function.
    pub fn register_function_context_type_params(
        &mut self,
        function_name: String,
        type_params: Vec<TypeParamDef>,
    ) {
        if type_params.is_empty() {
            self.function_type_param_contexts.remove(&function_name);
        } else {
            self.function_type_param_contexts
                .insert(function_name, type_params);
        }
    }

    /// Register a type
    pub fn register_type(&mut self, def: TypeDef) {
        let name = match &def {
            TypeDef::Struct { name, .. }
            | TypeDef::Enum { name, .. }
            | TypeDef::Union { name, .. } => name.clone(),
        };
        self.types.insert(name, def);
    }

    /// Register a Drop implementation for a type
    pub fn register_drop_impl(&mut self, type_name: String, drop_fn_name: String) {
        self.drop_impls.insert(type_name, drop_fn_name);
    }

    /// Get the drop function for a type, if it has one
    #[must_use]
    pub fn get_drop_impl(&self, type_name: &str) -> Option<&String> {
        self.drop_impls.get(type_name)
    }

    /// Look up a function
    #[must_use]
    pub fn get_function(&self, name: &str) -> Option<&FunctionDef> {
        self.functions.get(name)
    }

    /// Look up inherited generic parameters for a function.
    #[must_use]
    pub fn get_function_context_type_params(&self, name: &str) -> &[TypeParamDef] {
        self.function_type_param_contexts
            .get(name)
            .map(Vec::as_slice)
            .unwrap_or(&[])
    }

    /// Look up a type
    #[must_use]
    pub fn get_type(&self, name: &str) -> Option<&TypeDef> {
        self.types.get(name)
    }

    /// Register a trait implementation
    ///
    /// This is called when processing `impl Trait for Type { ... }` blocks.
    /// Methods in the impl are registered separately via register_function.
    /// Associated types are registered via `add_impl_associated_type`.
    pub fn register_trait_impl(&mut self, trait_name: String, self_ty: RustType) {
        let type_name = self_ty.name().unwrap_or_else(|| "anonymous".to_string());
        self.trait_impls.entry(type_name).or_default().insert(
            trait_name.clone(),
            TraitImplInfo {
                trait_name,
                self_ty,
                methods: HashMap::new(),
                associated_types: HashMap::new(),
            },
        );
    }

    /// Get trait implementation info
    #[must_use]
    pub fn get_trait_impl(&self, trait_name: &str, type_name: &str) -> Option<&TraitImplInfo> {
        self.trait_impls
            .get(type_name)
            .and_then(|impls| impls.get(trait_name))
    }

    /// Check if a type implements a trait
    #[must_use]
    pub fn implements_trait(&self, type_name: &str, trait_name: &str) -> bool {
        self.trait_impls
            .get(type_name)
            .is_some_and(|impls| impls.contains_key(trait_name))
    }

    /// Register a trait definition
    ///
    /// Stores the trait's method signatures and associated types for static-dispatch validation.
    /// Called when processing trait definitions.
    /// Example: `ctx.register_trait_def("Calculator".to_string(), vec![FunctionSignature { ... }]);`
    pub fn register_trait_def(&mut self, trait_name: String, methods: Vec<FunctionSignature>) {
        let trait_def = TraitDef::new(trait_name.clone(), methods);
        self.trait_defs.insert(trait_name, trait_def);
    }

    /// Register a full trait definition with associated types
    ///
    /// For traits with associated types (e.g., `Iterator::Item`), use this method
    /// instead of `register_trait_def`.
    pub fn register_full_trait_def(&mut self, trait_def: TraitDef) {
        self.trait_defs.insert(trait_def.name.clone(), trait_def);
    }

    /// Get the signature for a trait method
    #[must_use]
    pub fn get_trait_method_signature(
        &self,
        trait_name: &str,
        method_name: &str,
    ) -> Option<&FunctionSignature> {
        self.trait_defs
            .get(trait_name)
            .and_then(|def| def.methods.iter().find(|sig| sig.name == method_name))
    }

    /// Get the definition for an associated type in a trait
    #[must_use]
    pub fn get_trait_associated_type(
        &self,
        trait_name: &str,
        assoc_name: &str,
    ) -> Option<&AssociatedTypeDef> {
        self.trait_defs
            .get(trait_name)
            .and_then(|def| def.associated_types.iter().find(|a| a.name == assoc_name))
    }

    /// Get a trait definition by name
    #[must_use]
    pub fn get_trait_def(&self, trait_name: &str) -> Option<&TraitDef> {
        self.trait_defs.get(trait_name)
    }

    /// Find all traits implemented by a type
    #[must_use]
    pub fn traits_for_type(&self, type_name: &str) -> Vec<&String> {
        self.trait_impls
            .get(type_name)
            .map(|impls| impls.keys().collect())
            .unwrap_or_default()
    }

    /// Look up cached method impls for a type across all of its trait impls.
    #[must_use]
    pub(crate) fn get_trait_method_impls(
        &self,
        type_name: &str,
        method_name: &str,
    ) -> Option<&HashMap<String, String>> {
        self.trait_method_impls
            .get(type_name)
            .and_then(|methods| methods.get(method_name))
    }

    /// Register a method for a trait implementation
    ///
    /// Called after `register_trait_impl` to add methods to the impl.
    /// The `impl_fn_name` is the actual function registered in `functions`.
    ///
    /// # Panics
    /// Panics if the trait impl was not previously registered via `register_trait_impl`.
    /// This catches programming errors where methods are added before the impl.
    pub fn add_impl_method(
        &mut self,
        trait_name: &str,
        type_name: &str,
        method_name: String,
        impl_fn_name: String,
    ) {
        {
            let info = self
                .trait_impls
                .get_mut(type_name)
                .and_then(|impls| impls.get_mut(trait_name))
                .expect("invariant: trait impl must be registered before adding methods");
            info.methods
                .insert(method_name.clone(), impl_fn_name.clone());
        }
        self.trait_method_impls
            .entry(type_name.to_string())
            .or_default()
            .entry(method_name)
            .or_default()
            .insert(trait_name.to_string(), impl_fn_name);
    }

    /// Add an associated type to a trait implementation
    ///
    /// # Example
    /// ```text
    /// // For `impl Iterator for Counter { type Item = i32; }`
    /// ctx.add_impl_associated_type(
    ///     "Iterator",
    ///     "Counter",
    ///     "Item",
    ///     vec![],
    ///     vec![],
    ///     RustType::Int(I32),
    /// );
    /// ```
    ///
    /// # Panics
    /// Panics if the trait impl was not previously registered via `register_trait_impl`.
    pub fn add_impl_associated_type(
        &mut self,
        trait_name: &str,
        type_name: &str,
        assoc_name: String,
        generic_params: Vec<GenericParam>,
        where_clause: Vec<WherePredicate>,
        concrete_ty: RustType,
    ) {
        let info = self
            .trait_impls
            .get_mut(type_name)
            .and_then(|impls| impls.get_mut(trait_name))
            .expect("invariant: trait impl must be registered before adding associated types");
        info.associated_types.insert(
            assoc_name,
            AssociatedTypeValue {
                generic_params,
                where_clause,
                ty: concrete_ty,
            },
        );
    }

    /// Get the concrete type for an associated type in a trait implementation.
    ///
    /// Returns the concrete type that a type provides for an associated type,
    /// instantiating generic associated type parameters from the supplied
    /// arguments. For example, `Counter`'s `Iterator::Item` would return `i32`,
    /// while a GAT like `type Item<'a, T> = &'a T` would substitute both `'a`
    /// and `T`.
    #[must_use]
    pub fn get_impl_associated_type(
        &self,
        trait_name: &str,
        type_name: &str,
        assoc_name: &str,
        assoc_type_args: &[RustType],
        assoc_lifetime_args: &[Lifetime],
    ) -> Option<RustType> {
        self.trait_impls
            .get(type_name)
            .and_then(|impls| impls.get(trait_name))
            .and_then(|info| info.associated_types.get(assoc_name))
            .and_then(|assoc| {
                let def = GatDef::from_generic_params(
                    assoc_name.to_string(),
                    &assoc.generic_params,
                    None,
                );
                Some(
                    GatSubstitution::new(&def, assoc_type_args, assoc_lifetime_args)?
                        .apply(&assoc.ty),
                )
            })
    }

    /// Resolve a generic associated type projection to its concrete type.
    ///
    /// This applies generic bindings from the impl self type as well as any
    /// generic arguments supplied on the associated type projection itself.
    #[must_use]
    pub fn resolve_gat(
        &self,
        self_ty: &RustType,
        trait_name: &str,
        assoc_name: &str,
        assoc_type_args: &[RustType],
        assoc_lifetime_args: &[Lifetime],
    ) -> Option<RustType> {
        let type_name = self_ty.name()?;
        self.trait_impls
            .get(&type_name)
            .and_then(|impls| impls.get(trait_name))
            .and_then(|info| {
                info.resolve_associated_type(
                    self_ty,
                    assoc_name,
                    assoc_type_args,
                    assoc_lifetime_args,
                )
            })
    }

    /// Resolve a type projection to its concrete type
    ///
    /// Given a type projection like `<Counter as Iterator>::Item`, this method
    /// looks up the concrete type that `Counter` provides for `Iterator::Item`.
    ///
    /// # Example
    /// ```text
    /// If we have: impl Iterator for Counter { type Item = i32; }
    /// Then: resolve_type_projection(Counter, "Iterator", "Item") = Some(i32)
    /// ```
    ///
    /// Returns `None` if:
    /// - The self_ty doesn't have a name (e.g., primitive types without impls)
    /// - The type doesn't implement the specified trait
    /// - The impl doesn't provide the specified associated type
    #[must_use]
    pub fn resolve_type_projection(
        &self,
        self_ty: &RustType,
        trait_name: &str,
        assoc_name: &str,
        assoc_type_args: &[RustType],
        assoc_lifetime_args: &[Lifetime],
    ) -> Option<RustType> {
        self.resolve_gat(
            self_ty,
            trait_name,
            assoc_name,
            assoc_type_args,
            assoc_lifetime_args,
        )
    }

    /// Normalize a type by recursively resolving all type projections
    ///
    /// This transforms types containing `TypeProjection` variants into their
    /// concrete forms by looking up associated type implementations.
    ///
    /// # Normalization Rules
    ///
    /// - `TypeProjection`: Resolves to concrete type from trait impl
    /// - `Reference`: Recursively normalizes inner type
    /// - `Box`, `Option`, `Vec`: Recursively normalizes inner type
    /// - `Result`: Recursively normalizes both ok and err types
    /// - `Array`, `Slice`: Recursively normalizes element type
    /// - `Tuple`: Recursively normalizes all element types
    /// - `Function`: Recursively normalizes params and return type
    /// - `Named`: Recursively normalizes type_args (e.g., `Vec<T::Item>`)
    /// - `Closure`: Recursively normalizes params, return, and capture types
    /// - Other types: Returned unchanged
    ///
    /// If a projection cannot be resolved (missing impl), the projection
    /// is returned unchanged. This allows partial normalization.
    #[must_use]
    pub fn normalize_type(&self, ty: &RustType) -> RustType {
        match ty {
            RustType::TypeProjection {
                self_ty,
                trait_name,
                assoc_name,
                assoc_type_args,
                assoc_lifetime_args,
                ..
            } => {
                let normalized_self = self.normalize_type(self_ty);
                let normalized_assoc_type_args = assoc_type_args
                    .iter()
                    .map(|arg| self.normalize_type(arg))
                    .collect::<Vec<_>>();
                self.resolve_gat(
                    &normalized_self,
                    trait_name,
                    assoc_name,
                    &normalized_assoc_type_args,
                    assoc_lifetime_args,
                )
                .unwrap_or_else(|| RustType::TypeProjection {
                    self_ty: Box::new(normalized_self),
                    trait_name: trait_name.clone(),
                    assoc_name: assoc_name.clone(),
                    assoc_type_args: normalized_assoc_type_args,
                    assoc_lifetime_args: assoc_lifetime_args.clone(),
                    const_args: vec![],
                })
            }
            RustType::Reference {
                lifetime,
                mutability,
                inner,
            } => RustType::Reference {
                lifetime: lifetime.clone(),
                mutability: *mutability,
                inner: Box::new(self.normalize_type(inner)),
            },
            RustType::RawPtr { mutability, inner } => RustType::RawPtr {
                mutability: *mutability,
                inner: Box::new(self.normalize_type(inner)),
            },
            RustType::Box { inner } => RustType::Box {
                inner: Box::new(self.normalize_type(inner)),
            },
            RustType::Cell { inner } => RustType::Cell {
                inner: Box::new(self.normalize_type(inner)),
            },
            RustType::RefCell { inner } => RustType::RefCell {
                inner: Box::new(self.normalize_type(inner)),
            },
            RustType::UnsafeCell { inner } => RustType::UnsafeCell {
                inner: Box::new(self.normalize_type(inner)),
            },
            RustType::Option { inner } => RustType::Option {
                inner: Box::new(self.normalize_type(inner)),
            },
            RustType::Vec { element } => RustType::Vec {
                element: Box::new(self.normalize_type(element)),
            },
            RustType::Result { ok, err } => RustType::Result {
                ok: Box::new(self.normalize_type(ok)),
                err: Box::new(self.normalize_type(err)),
            },
            RustType::Array { element, len } => RustType::Array {
                element: Box::new(self.normalize_type(element)),
                len: len.clone(),
            },
            RustType::Slice { elem } => RustType::Slice {
                elem: Box::new(self.normalize_type(elem)),
            },
            RustType::Tuple(elems) => {
                RustType::Tuple(elems.iter().map(|e| self.normalize_type(e)).collect())
            }
            RustType::Function { params, ret } => RustType::Function {
                params: params.iter().map(|p| self.normalize_type(p)).collect(),
                ret: Box::new(self.normalize_type(ret)),
            },
            // Named types may have type_args containing projections
            RustType::Named {
                name,
                type_args,
                lifetime_args,
                const_args,
            } => RustType::Named {
                name: name.clone(),
                type_args: type_args.iter().map(|t| self.normalize_type(t)).collect(),
                lifetime_args: lifetime_args.clone(),
                const_args: const_args.clone(),
            },
            // Closure params/ret may contain projections
            RustType::Closure {
                params,
                ret,
                captures,
                kind,
            } => RustType::Closure {
                params: params.iter().map(|p| self.normalize_type(p)).collect(),
                ret: Box::new(self.normalize_type(ret)),
                captures: captures
                    .iter()
                    .map(|(name, ty, mutability)| {
                        (name.clone(), self.normalize_type(ty), *mutability)
                    })
                    .collect(),
                kind: *kind,
            },
            // Types that don't contain nested types (primitives, TypeParam, etc.)
            _ => ty.clone(),
        }
    }

    /// Resolve a method call on a type through trait implementations
    ///
    /// Returns the implementing function name if the method is found in any
    /// trait implemented by the type. Returns None for inherent methods.
    ///
    /// Resolution order:
    /// 1. Inherent methods (handled by caller checking functions directly)
    /// 2. Trait methods (this function)
    #[must_use]
    pub fn resolve_trait_method(&self, type_name: &str, method_name: &str) -> Option<&String> {
        self.resolve_trait_method_with_info(type_name, method_name)
            .map(|(impl_fn, _)| impl_fn)
    }

    /// Resolve a method call on a type through trait implementations with trait info
    ///
    /// Returns the implementing function name AND the trait name if the method
    /// is found in any trait implemented by the type.
    ///
    /// # Note on Ambiguity
    ///
    /// If a type implements multiple traits with methods of the same name, this
    /// function returns the first trait-name match found for that type. In real Rust,
    /// ambiguous method calls are compile-time errors requiring explicit trait
    /// qualification (e.g., `Trait::method(&x)`).
    #[must_use]
    pub fn resolve_trait_method_with_info(
        &self,
        type_name: &str,
        method_name: &str,
    ) -> Option<(&String, &str)> {
        self.get_trait_method_impls(type_name, method_name)?
            .iter()
            .next()
            .map(|(trait_name, impl_fn)| (impl_fn, trait_name.as_str()))
    }
}

impl Default for ExecContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Statement execution result
#[must_use]
#[derive(Debug, Clone)]
pub enum StmtResult {
    /// Statement completed normally
    Ok,
    /// Return from function
    Return(Value),
    /// Break from loop (with optional label and value)
    Break {
        label: Option<String>,
        value: Option<Value>,
    },
    /// Continue loop (with optional label)
    Continue { label: Option<String> },
    /// Panic occurred (abort semantics - immediate termination)
    Panic(String),
    /// Error during execution
    Error(String),
}

impl StmtResult {
    #[must_use]
    pub fn is_ok(&self) -> bool {
        matches!(self, StmtResult::Ok)
    }

    #[must_use]
    pub fn is_control_flow(&self) -> bool {
        matches!(
            self,
            StmtResult::Return(_) | StmtResult::Break { .. } | StmtResult::Continue { .. }
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::UintType;

    #[test]
    fn test_exec_context() {
        let mut ctx = ExecContext::new();

        let func = FunctionDef {
            name: "add".to_string(),
            params: vec![
                ("a".to_string(), RustType::Uint(UintType::U32)),
                ("b".to_string(), RustType::Uint(UintType::U32)),
            ],
            ret_ty: RustType::Uint(UintType::U32),
            body: Expr::Literal(Value::u32(0)), // Placeholder
            is_unsafe: false,
            is_async: false,
            type_params: vec![],
        };

        ctx.register_function(func);
        assert!(
            ctx.get_function("add").is_some(),
            "registered function 'add' should be retrievable"
        );
    }

    #[test]
    fn test_trait_def_basic() {
        use crate::types::{FunctionSignature, IntType, ReceiverMode};

        let trait_def = TraitDef::new(
            "Iterator".to_string(),
            vec![FunctionSignature {
                name: "next".to_string(),
                receiver: ReceiverMode::ByMut,
                params: vec![],
                ret: RustType::Option {
                    inner: Box::new(RustType::Int(IntType::I32)),
                },
                is_async: false,
                type_params: vec![],
            }],
        );

        assert_eq!(trait_def.name, "Iterator");
        assert_eq!(trait_def.methods.len(), 1);
        assert_eq!(trait_def.associated_types.len(), 0);
    }

    #[test]
    fn test_trait_def_with_associated_types() {
        use crate::types::{FunctionSignature, IntType, ReceiverMode};

        let trait_def = TraitDef::with_associated_types(
            "Iterator".to_string(),
            vec![FunctionSignature {
                name: "next".to_string(),
                receiver: ReceiverMode::ByMut,
                params: vec![],
                ret: RustType::Option {
                    inner: Box::new(RustType::Int(IntType::I32)),
                },
                is_async: false,
                type_params: vec![],
            }],
            vec![AssociatedTypeDef::new("Item".to_string(), vec![])],
        );

        assert_eq!(trait_def.name, "Iterator");
        assert_eq!(trait_def.methods.len(), 1);
        assert_eq!(trait_def.associated_types.len(), 1);
        assert_eq!(trait_def.associated_types[0].name, "Item");
    }

    #[test]
    fn test_associated_type_def_with_bounds() {
        let assoc = AssociatedTypeDef::with_bounds(
            "Item".to_string(),
            vec![],
            vec!["Clone".to_string(), "Debug".to_string()],
        );

        assert_eq!(assoc.name, "Item");
        assert_eq!(assoc.bounds.len(), 2);
        assert!(
            assoc.default.is_none(),
            "with_bounds should not set default"
        );
    }

    #[test]
    fn test_register_full_trait_def() {
        use crate::types::{FunctionSignature, ReceiverMode};

        let mut ctx = ExecContext::new();

        let trait_def = TraitDef::with_associated_types(
            "Iterator".to_string(),
            vec![FunctionSignature {
                name: "next".to_string(),
                receiver: ReceiverMode::ByMut,
                params: vec![],
                ret: RustType::Unit,
                is_async: false,
                type_params: vec![],
            }],
            vec![AssociatedTypeDef::new("Item".to_string(), vec![])],
        );

        ctx.register_full_trait_def(trait_def);

        // Verify trait def is registered
        let def = ctx
            .get_trait_def("Iterator")
            .expect("Iterator trait def should be registered");
        assert_eq!(def.associated_types.len(), 1);

        // Verify method lookup works
        assert!(
            ctx.get_trait_method_signature("Iterator", "next").is_some(),
            "Iterator::next method signature should be retrievable"
        );

        // Verify associated type lookup works
        let assoc = ctx
            .get_trait_associated_type("Iterator", "Item")
            .expect("Iterator::Item associated type should be retrievable");
        assert_eq!(assoc.name, "Item");
    }

    #[test]
    fn test_impl_associated_type() {
        use crate::types::IntType;

        let mut ctx = ExecContext::new();

        // Register Counter type
        ctx.register_type(TypeDef::Struct {
            name: "Counter".to_string(),
            fields: vec![("count".to_string(), RustType::Int(IntType::I32))],
            type_params: vec![],
            const_params: vec![],
        });

        // Register Iterator trait impl for Counter
        ctx.register_trait_impl(
            "Iterator".to_string(),
            RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );

        // Add associated type: Counter's Item = i32
        ctx.add_impl_associated_type(
            "Iterator",
            "Counter",
            "Item".to_string(),
            vec![],
            vec![],
            RustType::Int(IntType::I32),
        );

        // Verify we can retrieve the associated type
        let item_ty = ctx.get_impl_associated_type("Iterator", "Counter", "Item", &[], &[]);
        assert!(
            matches!(item_ty, Some(RustType::Int(IntType::I32))),
            "expected Some(Int(I32)), got: {:?}",
            item_ty
        );
    }

    #[test]
    fn test_resolve_type_projection() {
        use crate::types::IntType;

        let mut ctx = ExecContext::new();

        // Register Counter type
        ctx.register_type(TypeDef::Struct {
            name: "Counter".to_string(),
            fields: vec![("count".to_string(), RustType::Int(IntType::I32))],
            type_params: vec![],
            const_params: vec![],
        });

        // Register Iterator trait impl for Counter with associated type
        ctx.register_trait_impl(
            "Iterator".to_string(),
            RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "Iterator",
            "Counter",
            "Item".to_string(),
            vec![],
            vec![],
            RustType::Int(IntType::I32),
        );

        // Resolve <Counter as Iterator>::Item
        let counter_ty = RustType::Named {
            name: "Counter".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        };
        let resolved = ctx.resolve_type_projection(&counter_ty, "Iterator", "Item", &[], &[]);
        assert!(
            matches!(resolved, Some(RustType::Int(IntType::I32))),
            "expected Some(Int(I32)), got: {:?}",
            resolved
        );

        // Unresolved projection returns None
        let no_impl = ctx.resolve_type_projection(&counter_ty, "IntoIterator", "Item", &[], &[]);
        assert!(
            no_impl.is_none(),
            "unregistered trait impl should return None for projection"
        );
    }

    #[test]
    fn test_resolve_type_projection_simple_gat() {
        use crate::types::{IntType, TypeVar};

        let mut ctx = ExecContext::new();

        ctx.register_type(TypeDef::Struct {
            name: "Bar".to_string(),
            fields: vec![],
            type_params: vec![],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "Foo".to_string(),
            RustType::Named {
                name: "Bar".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );

        let item_param = TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        };
        ctx.add_impl_associated_type(
            "Foo",
            "Bar",
            "Item".to_string(),
            vec![GenericParam::type_param(item_param.clone())],
            vec![],
            RustType::Option {
                inner: Box::new(RustType::TypeParam(TypeVar {
                    id: item_param.id,
                    name: Some(item_param.name.clone()),
                })),
            },
        );

        let bar_ty = RustType::Named {
            name: "Bar".to_string(),
            type_args: vec![],
            lifetime_args: vec![],
            const_args: vec![],
        };
        let resolved = ctx.resolve_type_projection(
            &bar_ty,
            "Foo",
            "Item",
            &[RustType::Int(IntType::I32)],
            &[],
        );
        assert_eq!(
            resolved,
            Some(RustType::Option {
                inner: Box::new(RustType::Int(IntType::I32)),
            })
        );

        let projection = RustType::TypeProjection {
            self_ty: Box::new(bar_ty),
            trait_name: "Foo".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![RustType::Int(IntType::I32)],
            assoc_lifetime_args: vec![],
            const_args: vec![],
        };
        assert_eq!(
            ctx.normalize_type(&projection),
            RustType::Option {
                inner: Box::new(RustType::Int(IntType::I32)),
            }
        );
    }

    #[test]
    fn test_resolve_type_projection_lifetime_gat() {
        use crate::types::{IntType, Lifetime, Mutability};

        let mut ctx = ExecContext::new();

        ctx.register_type(TypeDef::Struct {
            name: "Book".to_string(),
            fields: vec![],
            type_params: vec![],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "Lending".to_string(),
            RustType::Named {
                name: "Book".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "Lending",
            "Book",
            "Item".to_string(),
            vec![GenericParam::lifetime("a")],
            vec![],
            RustType::Reference {
                lifetime: Lifetime::Named("a".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Int(IntType::I32)),
            },
        );

        let projection = RustType::TypeProjection {
            self_ty: Box::new(RustType::Named {
                name: "Book".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            }),
            trait_name: "Lending".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![Lifetime::Named("loan".to_string())],
            const_args: vec![],
        };

        assert_eq!(
            ctx.normalize_type(&projection),
            RustType::Reference {
                lifetime: Lifetime::Named("loan".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Int(IntType::I32)),
            }
        );
    }

    #[test]
    fn test_resolve_type_projection_generic_container_gat() {
        use crate::types::{IntType, Lifetime, Mutability, TypeVar};

        let mut ctx = ExecContext::new();
        let container_param = TypeParamDef {
            id: 0,
            name: "T".to_string(),
            bounds: vec![],
        };

        ctx.register_type(TypeDef::Struct {
            name: "Container".to_string(),
            fields: vec![],
            type_params: vec![container_param.clone()],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "LendingIterator".to_string(),
            RustType::Named {
                name: "Container".to_string(),
                type_args: vec![RustType::TypeParam(TypeVar {
                    id: container_param.id,
                    name: Some(container_param.name.clone()),
                })],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "LendingIterator",
            "Container",
            "Item".to_string(),
            vec![GenericParam::lifetime("a")],
            vec![],
            RustType::Reference {
                lifetime: Lifetime::Named("a".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::TypeParam(TypeVar {
                    id: container_param.id,
                    name: Some(container_param.name.clone()),
                })),
            },
        );

        let projection = RustType::TypeProjection {
            self_ty: Box::new(RustType::Named {
                name: "Container".to_string(),
                type_args: vec![RustType::Int(IntType::I32)],
                lifetime_args: vec![],
                const_args: vec![],
            }),
            trait_name: "LendingIterator".to_string(),
            assoc_name: "Item".to_string(),
            assoc_type_args: vec![],
            assoc_lifetime_args: vec![Lifetime::Named("iter".to_string())],
            const_args: vec![],
        };

        assert_eq!(
            ctx.normalize_type(&projection),
            RustType::Reference {
                lifetime: Lifetime::Named("iter".to_string()),
                mutability: Mutability::Shared,
                inner: Box::new(RustType::Int(IntType::I32)),
            }
        );
    }

    #[test]
    fn test_normalize_type_basic() {
        use crate::types::IntType;

        let mut ctx = ExecContext::new();

        // Register Counter with Iterator impl
        ctx.register_type(TypeDef::Struct {
            name: "Counter".to_string(),
            fields: vec![],
            type_params: vec![],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "Iterator".to_string(),
            RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "Iterator",
            "Counter",
            "Item".to_string(),
            vec![],
            vec![],
            RustType::Int(IntType::I32),
        );

        // Create a type projection: <Counter as Iterator>::Item
        let projection = RustType::TypeProjection {
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
        };

        // Normalize should resolve to i32
        let normalized = ctx.normalize_type(&projection);
        assert!(matches!(normalized, RustType::Int(IntType::I32)));
    }

    #[test]
    fn test_normalize_type_nested() {
        use crate::types::{IntType, Lifetime, Mutability};

        let mut ctx = ExecContext::new();

        // Register Counter with Iterator impl
        ctx.register_type(TypeDef::Struct {
            name: "Counter".to_string(),
            fields: vec![],
            type_params: vec![],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "Iterator".to_string(),
            RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "Iterator",
            "Counter",
            "Item".to_string(),
            vec![],
            vec![],
            RustType::Int(IntType::I32),
        );

        // Create Option<<Counter as Iterator>::Item>
        let nested = RustType::Option {
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
        };

        // Normalize should produce Option<i32>
        let normalized = ctx.normalize_type(&nested);
        match normalized {
            RustType::Option { inner } => {
                assert!(matches!(*inner, RustType::Int(IntType::I32)));
            }
            _ => panic!("Expected Option type"),
        }

        // Test with Reference<TypeProjection>
        let ref_nested = RustType::Reference {
            lifetime: Lifetime::Static,
            mutability: Mutability::Shared,
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
        };

        let normalized_ref = ctx.normalize_type(&ref_nested);
        match normalized_ref {
            RustType::Reference { inner, .. } => {
                assert!(matches!(*inner, RustType::Int(IntType::I32)));
            }
            _ => panic!("Expected Reference type"),
        }
    }

    #[test]
    fn test_normalize_type_unresolved() {
        let ctx = ExecContext::new();

        // Create a projection that cannot be resolved (no impl registered)
        let projection = RustType::TypeProjection {
            self_ty: Box::new(RustType::Named {
                name: "Unknown".to_string(),
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

        // Normalize should return the projection unchanged
        let normalized = ctx.normalize_type(&projection);
        assert!(matches!(normalized, RustType::TypeProjection { .. }));
    }

    #[test]
    fn test_normalize_type_idempotent() {
        use crate::types::IntType;

        let mut ctx = ExecContext::new();

        // Register Counter with Iterator impl
        ctx.register_type(TypeDef::Struct {
            name: "Counter".to_string(),
            fields: vec![],
            type_params: vec![],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "Iterator".to_string(),
            RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "Iterator",
            "Counter",
            "Item".to_string(),
            vec![],
            vec![],
            RustType::Int(IntType::I32),
        );

        let projection = RustType::TypeProjection {
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
        };

        // Normalization should be idempotent
        let once = ctx.normalize_type(&projection);
        let twice = ctx.normalize_type(&once);
        assert!(matches!(once, RustType::Int(IntType::I32)));
        assert!(matches!(twice, RustType::Int(IntType::I32)));
    }

    #[test]
    fn test_normalize_type_named_with_type_args() {
        use crate::types::IntType;

        let mut ctx = ExecContext::new();

        // Register Counter with Iterator impl
        ctx.register_type(TypeDef::Struct {
            name: "Counter".to_string(),
            fields: vec![],
            type_params: vec![],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "Iterator".to_string(),
            RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "Iterator",
            "Counter",
            "Item".to_string(),
            vec![],
            vec![],
            RustType::Int(IntType::I32),
        );

        // Create MyStruct<T> where T = <Counter as Iterator>::Item
        let named_with_projection = RustType::Named {
            name: "MyStruct".to_string(),
            type_args: vec![RustType::TypeProjection {
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
            }],
            lifetime_args: vec![],
            const_args: vec![],
        };

        // Normalize should produce MyStruct<i32>
        let normalized = ctx.normalize_type(&named_with_projection);
        match normalized {
            RustType::Named {
                name, type_args, ..
            } => {
                assert_eq!(name, "MyStruct");
                assert_eq!(type_args.len(), 1);
                assert!(matches!(type_args[0], RustType::Int(IntType::I32)));
            }
            _ => panic!("Expected Named type"),
        }
    }

    #[test]
    fn test_associated_type_def_with_default() {
        use crate::types::IntType;

        let assoc = AssociatedTypeDef::with_default(
            "Item".to_string(),
            vec![],
            RustType::Int(IntType::I32),
        );

        assert_eq!(assoc.name, "Item");
        assert!(assoc.bounds.is_empty());
        assert!(
            matches!(assoc.default, Some(RustType::Int(IntType::I32))),
            "expected default Some(Int(I32)), got: {:?}",
            assoc.default
        );
    }

    #[test]
    fn test_associated_type_def_with_bounds_and_default() {
        use crate::types::IntType;

        let assoc = AssociatedTypeDef::with_bounds_and_default(
            "Item".to_string(),
            vec![],
            vec!["Clone".to_string(), "Debug".to_string()],
            RustType::Int(IntType::I32),
        );

        assert_eq!(assoc.name, "Item");
        assert_eq!(assoc.bounds.len(), 2);
        assert!(
            matches!(assoc.default, Some(RustType::Int(IntType::I32))),
            "expected default Some(Int(I32)), got: {:?}",
            assoc.default
        );
    }

    #[test]
    fn test_trait_def_serialization() {
        use crate::types::{FunctionSignature, IntType, ReceiverMode};

        let trait_def = TraitDef::with_associated_types(
            "Iterator".to_string(),
            vec![FunctionSignature {
                name: "next".to_string(),
                receiver: ReceiverMode::ByMut,
                params: vec![],
                ret: RustType::Option {
                    inner: Box::new(RustType::Int(IntType::I32)),
                },
                is_async: false,
                type_params: vec![],
            }],
            vec![AssociatedTypeDef::with_default(
                "Item".to_string(),
                vec![],
                RustType::Unit,
            )],
        );

        // Test serialization roundtrip
        let json = serde_json::to_string(&trait_def).expect("serialization failed");
        let deserialized: TraitDef = serde_json::from_str(&json).expect("deserialization failed");

        assert_eq!(deserialized.name, "Iterator");
        assert_eq!(deserialized.methods.len(), 1);
        assert_eq!(deserialized.associated_types.len(), 1);
        assert_eq!(deserialized.associated_types[0].name, "Item");
    }

    #[test]
    fn test_trait_impl_info_serialization() {
        use crate::types::IntType;

        let mut impl_info = TraitImplInfo {
            trait_name: "Iterator".to_string(),
            self_ty: RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
            methods: HashMap::new(),
            associated_types: HashMap::new(),
        };
        impl_info.associated_types.insert(
            "Item".to_string(),
            AssociatedTypeValue {
                generic_params: vec![],
                where_clause: vec![],
                ty: RustType::Int(IntType::I32),
            },
        );

        // Test serialization roundtrip
        let json = serde_json::to_string(&impl_info).expect("serialization failed");
        let deserialized: TraitImplInfo =
            serde_json::from_str(&json).expect("deserialization failed");

        assert_eq!(deserialized.trait_name, "Iterator");
        assert!(deserialized.associated_types.contains_key("Item"));
    }

    #[test]
    fn test_normalize_type_closure() {
        use crate::types::{ClosureKind, IntType};

        let mut ctx = ExecContext::new();

        // Register Counter with Iterator impl
        ctx.register_type(TypeDef::Struct {
            name: "Counter".to_string(),
            fields: vec![],
            type_params: vec![],
            const_params: vec![],
        });
        ctx.register_trait_impl(
            "Iterator".to_string(),
            RustType::Named {
                name: "Counter".to_string(),
                type_args: vec![],
                lifetime_args: vec![],
                const_args: vec![],
            },
        );
        ctx.add_impl_associated_type(
            "Iterator",
            "Counter",
            "Item".to_string(),
            vec![],
            vec![],
            RustType::Int(IntType::I32),
        );

        // Create closure with projection in return type
        let closure_with_projection = RustType::Closure {
            params: vec![],
            ret: Box::new(RustType::TypeProjection {
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
            captures: vec![],
            kind: ClosureKind::Fn,
        };

        // Normalize should resolve the return type
        let normalized = ctx.normalize_type(&closure_with_projection);
        match normalized {
            RustType::Closure { ret, .. } => {
                assert!(matches!(*ret, RustType::Int(IntType::I32)));
            }
            _ => panic!("Expected Closure type"),
        }
    }
}
