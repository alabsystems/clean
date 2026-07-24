// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Item declarations (function, struct, enum, impl, etc.)

use crate::expr::{Expr, InlineAsm};
use crate::types::RustType;
use serde::{Deserialize, Serialize};

/// Item declaration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Item {
    /// Function definition
    Fn {
        name: String,
        params: Vec<(String, RustType)>,
        ret: RustType,
        body: Expr,
        /// Whether this function is marked `unsafe fn`
        is_unsafe: bool,
        /// Whether this function is marked `async fn`
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        is_async: bool,
        /// Generic type parameters (empty for non-generic functions)
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_params: Vec<crate::types::TypeParamDef>,
    },

    /// Struct definition
    Struct {
        name: String,
        fields: Vec<(String, RustType)>,
        /// Generic type parameters (empty for non-generic structs)
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_params: Vec<crate::types::TypeParamDef>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_params: Vec<crate::types::ConstParamDef>,
    },

    /// Enum definition
    Enum {
        name: String,
        variants: Vec<crate::types::EnumVariant>,
        /// Generic type parameters (empty for non-generic enums)
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_params: Vec<crate::types::TypeParamDef>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_params: Vec<crate::types::ConstParamDef>,
    },

    /// Trait definition metadata
    TraitDef(crate::stmt::TraitDef),

    /// Associated type assignment inside a trait impl block
    ///
    /// Example: `impl Iterator for Counter { type Item = u32; }`
    ImplAssociatedType {
        name: String,
        ty: RustType,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        generic_params: Vec<crate::stmt::GenericParam>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        where_clause: Vec<crate::stmt::WherePredicate>,
    },

    /// Union definition
    ///
    /// Unions are like structs but all fields share the same memory.
    /// Accessing union fields requires unsafe context.
    Union {
        name: String,
        fields: Vec<(String, RustType)>,
        /// Generic type parameters (empty for non-generic unions)
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_params: Vec<crate::types::TypeParamDef>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_params: Vec<crate::types::ConstParamDef>,
    },

    /// Impl block (inherent or trait implementation)
    ///
    /// Inherent impl: `impl Type { ... }` - trait_name is None
    /// Trait impl: `impl Trait for Type { ... }` - trait_name is Some
    Impl {
        /// The implementing type
        self_ty: RustType,
        /// Optional trait being implemented (None for inherent impls)
        trait_name: Option<String>,
        /// Items in the impl block
        items: Vec<Item>,
        /// Generic type parameters (empty for non-generic impl blocks)
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        type_params: Vec<crate::types::TypeParamDef>,
        #[serde(default, skip_serializing_if = "Vec::is_empty")]
        const_params: Vec<crate::types::ConstParamDef>,
    },

    /// Const item
    Const {
        name: String,
        ty: RustType,
        value: Expr,
    },

    /// Static item
    Static {
        name: String,
        ty: RustType,
        mutable: bool,
        value: Expr,
    },

    /// Type alias (`type Name = Ty;`).
    ///
    /// Type aliases are resolved structurally during source ingestion (the
    /// referenced type is recorded in the parser's alias table and substituted
    /// wherever the alias name appears), so this item carries no runtime
    /// behavior. It is preserved in the AST for fidelity and so that
    /// block-scoped aliases are observable. The `block_scoped` flag records
    /// whether the alias was declared inside a block rather than at module
    /// scope; a block-scoped alias is only visible within its enclosing block.
    TypeAlias {
        name: String,
        ty: RustType,
        /// Whether this alias was declared inside a block (vs. module scope).
        #[serde(default, skip_serializing_if = "std::ops::Not::not")]
        block_scoped: bool,
    },

    GlobalAsm(InlineAsm),
}
