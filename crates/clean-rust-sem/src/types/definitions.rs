// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Compound type definitions: structs, enums, function signatures,
//! and their associated metadata.

use serde::{Deserialize, Serialize};

use super::{RustType, TypeParamDef, TypeVar};

/// Struct field definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructField {
    pub name: String,
    pub ty: RustType,
    pub visibility: Visibility,
}

/// Visibility modifier
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub enum Visibility {
    /// Private (default)
    Private,
    /// pub
    Public,
    /// pub(crate)
    Crate,
    /// pub(super)
    Super,
}

/// Struct definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StructDef {
    pub name: String,
    pub type_params: Vec<TypeVar>,
    pub lifetime_params: Vec<String>,
    pub fields: Vec<StructField>,
    /// Derived traits (Copy, Clone, Debug, etc.)
    pub derives: Vec<String>,
}

impl StructDef {
    /// Check if struct is Copy
    pub fn is_copy(&self) -> bool {
        self.derives.contains(&"Copy".to_string()) && self.fields.iter().all(|f| f.ty.is_copy())
    }

    /// Calculate struct size (None if contains unsized field)
    pub fn size(&self) -> Option<usize> {
        let mut total = 0;
        for field in &self.fields {
            total += field.ty.size()?;
        }
        Some(total)
    }
}

/// Enum variant
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum EnumVariant {
    /// Unit variant: Foo or Foo = 42
    Unit {
        name: String,
        discriminant: Option<i128>,
    },
    /// Tuple variant: Foo(T1, T2)
    Tuple {
        name: String,
        fields: Vec<RustType>,
        discriminant: Option<i128>,
    },
    /// Struct variant: Foo { x: T1, y: T2 }
    Struct {
        name: String,
        fields: Vec<StructField>,
        discriminant: Option<i128>,
    },
}

/// Enum definition
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EnumDef {
    pub name: String,
    pub type_params: Vec<TypeVar>,
    pub lifetime_params: Vec<String>,
    pub variants: Vec<EnumVariant>,
    pub derives: Vec<String>,
}

/// Receiver mode for trait methods.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default, Serialize, Deserialize)]
pub enum ReceiverMode {
    /// No `self` receiver; a static associated function.
    Static,
    /// `self`
    #[default]
    ByValue,
    /// `&self`
    ByRef,
    /// `&mut self`
    ByMut,
}

impl ReceiverMode {
    pub const fn has_self_receiver(self) -> bool {
        !matches!(self, Self::Static)
    }
}

/// Function signature for trait methods
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct FunctionSignature {
    pub name: String,
    #[serde(default)]
    pub receiver: ReceiverMode,
    pub params: Vec<RustType>,
    pub ret: RustType,
    /// Whether this method is `async fn`
    #[serde(default, skip_serializing_if = "std::ops::Not::not")]
    pub is_async: bool,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub type_params: Vec<TypeParamDef>,
}

#[cfg(test)]
mod tests {
    use super::super::*;

    #[test]
    fn test_struct_definition() {
        let point_struct = StructDef {
            name: "Point".to_string(),
            type_params: vec![],
            lifetime_params: vec![],
            fields: vec![
                StructField {
                    name: "x".to_string(),
                    ty: RustType::Float(FloatType::F64),
                    visibility: Visibility::Public,
                },
                StructField {
                    name: "y".to_string(),
                    ty: RustType::Float(FloatType::F64),
                    visibility: Visibility::Public,
                },
            ],
            derives: vec!["Copy".to_string(), "Clone".to_string()],
        };

        assert_eq!(point_struct.size(), Some(16));
        assert!(point_struct.is_copy());
    }
}
