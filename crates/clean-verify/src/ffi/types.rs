// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Core data types for FFI boundary verification.

use std::collections::BTreeMap;

use super::error::FfiBoundaryParseError;

/// Parsed FFI boundary specification for one Rust source fragment.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FfiBoundarySpec {
    /// Composite and alias type declarations visible to the FFI checker.
    pub types: BTreeMap<String, FfiTypeDecl>,
    /// All parsed `extern { ... }` blocks.
    pub extern_blocks: Vec<FfiExternBlock>,
}

impl FfiBoundarySpec {
    /// Parse a Rust source fragment into an FFI boundary spec.
    pub fn from_source(source: &str) -> Result<Self, FfiBoundaryParseError> {
        super::parser::parse_source(source)
    }

    /// Lookup an extern function contract by name.
    #[must_use]
    pub fn function(&self, name: &str) -> Option<&FfiFunctionContract> {
        self.extern_blocks
            .iter()
            .flat_map(|block| block.functions.iter())
            .find(|function| function.name == name)
    }

    /// Mutably lookup an extern function contract by name.
    pub fn function_mut(&mut self, name: &str) -> Option<&mut FfiFunctionContract> {
        self.extern_blocks
            .iter_mut()
            .flat_map(|block| block.functions.iter_mut())
            .find(|function| function.name == name)
    }

    pub(crate) fn insert_type(&mut self, decl: FfiTypeDecl) -> Result<(), FfiBoundaryParseError> {
        let name = decl.name.clone();
        if self.types.insert(name.clone(), decl).is_some() {
            return Err(FfiBoundaryParseError::DuplicateTypeDecl(name));
        }
        Ok(())
    }

    pub(crate) fn resolve_type(&self, name: &str) -> Option<&FfiTypeDecl> {
        self.types.get(name).or_else(|| {
            name.rsplit("::")
                .next()
                .and_then(|segment| self.types.get(segment))
        })
    }
}

/// One `extern { ... }` block.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiExternBlock {
    /// ABI for the block, usually `"C"`.
    pub abi: String,
    /// Foreign functions declared inside the block.
    pub functions: Vec<FfiFunctionContract>,
}

/// Contract for a single extern function declaration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiFunctionContract {
    /// Function name.
    pub name: String,
    /// ABI for the declaration.
    pub abi: String,
    /// Inputs.
    pub inputs: Vec<FfiParam>,
    /// Output type, if any.
    pub output: Option<FfiTypeRef>,
    /// Whether the function is variadic.
    pub variadic: bool,
    /// Preconditions the caller must establish before the call.
    pub preconditions: Vec<FfiPrecondition>,
    /// Postconditions the foreign callee must satisfy on return.
    pub postconditions: Vec<FfiPostcondition>,
}

impl FfiFunctionContract {
    /// Require a raw-pointer parameter to be non-null, aligned, and initialized.
    pub fn require_pointer_validity_for(&mut self, param: impl Into<String>) {
        self.preconditions.push(FfiPrecondition::PointerValidity {
            param: param.into(),
            non_null: true,
            aligned: true,
            initialized: true,
        });
    }

    /// Require a pointer result to be non-null, aligned, and initialized.
    pub fn require_pointer_valid_return(&mut self) {
        self.postconditions.push(FfiPostcondition::PointerValidity {
            non_null: true,
            aligned: true,
            initialized: true,
        });
    }

    /// Require that the callee does not unwind across the FFI boundary.
    pub fn require_no_unwind(&mut self) {
        if !self
            .postconditions
            .iter()
            .any(|cond| matches!(cond, FfiPostcondition::NoUnwind))
        {
            self.postconditions.push(FfiPostcondition::NoUnwind);
        }
    }

    pub(crate) fn has_pointer_precondition(&self, param: &str) -> bool {
        matches!(
            self.pointer_precondition_flags(param),
            Some((true, true, true))
        )
    }

    pub(crate) fn has_pointer_postcondition(&self) -> bool {
        matches!(self.pointer_postcondition_flags(), Some((true, true, true)))
    }

    pub(crate) fn has_no_unwind_postcondition(&self) -> bool {
        self.postconditions
            .iter()
            .any(|cond| matches!(cond, FfiPostcondition::NoUnwind))
    }

    pub(crate) fn pointer_precondition_flags(&self, param: &str) -> Option<(bool, bool, bool)> {
        self.preconditions.iter().find_map(|cond| match cond {
            FfiPrecondition::PointerValidity {
                param: target,
                non_null,
                aligned,
                initialized,
            } if target == param => Some((*non_null, *aligned, *initialized)),
            _ => None,
        })
    }

    pub(crate) fn pointer_postcondition_flags(&self) -> Option<(bool, bool, bool)> {
        self.postconditions.iter().find_map(|cond| match cond {
            FfiPostcondition::PointerValidity {
                non_null,
                aligned,
                initialized,
            } => Some((*non_null, *aligned, *initialized)),
            _ => None,
        })
    }
}

/// A foreign function parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiParam {
    /// Parameter name.
    pub name: String,
    /// Parameter type.
    pub ty: FfiTypeRef,
}

/// Preconditions that must hold before calling an extern function.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FfiPrecondition {
    /// A raw pointer argument must be valid for the callee to dereference.
    PointerValidity {
        param: String,
        non_null: bool,
        aligned: bool,
        initialized: bool,
    },
    /// A borrowed value must not dangle while the call is in flight.
    Lifetime { param: String, no_dangling: bool },
}

/// Postconditions that must hold after an extern function returns.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FfiPostcondition {
    /// The returned raw pointer is valid for use by Rust.
    PointerValidity {
        non_null: bool,
        aligned: bool,
        initialized: bool,
    },
    /// The returned borrowed value must not dangle.
    Lifetime { no_dangling: bool },
    /// The callee must not unwind across the FFI boundary.
    NoUnwind,
}

/// Concrete safety obligations derived from an FFI signature.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FfiSafetyCheck {
    /// A pointer argument or result must satisfy validity requirements.
    PointerValidity {
        function: String,
        target: FfiValueTarget,
        non_null: bool,
        aligned: bool,
        initialized: bool,
    },
    /// A borrowed value must not dangle across the boundary.
    Lifetime {
        function: String,
        target: FfiValueTarget,
        no_dangling: bool,
    },
    /// A named composite type must use a stable C-compatible layout.
    TypeLayoutCompatibility {
        function: String,
        ty: String,
        requires_repr_c: bool,
    },
    /// The boundary must not unwind.
    NoUnwinding { function: String },
}

/// What a safety check applies to.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum FfiValueTarget {
    /// A named parameter.
    Param(String),
    /// The return value.
    ReturnValue,
}

/// A locally declared type that appears in an FFI signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiTypeDecl {
    /// Type name.
    pub name: String,
    /// Whether the declaration uses `#[repr(C)]`.
    pub repr_c: bool,
    /// Whether the declaration is generic.
    pub is_generic: bool,
    /// Structural kind.
    pub kind: FfiTypeDeclKind,
}

/// Structural kind for a locally declared type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FfiTypeDeclKind {
    /// `struct Foo { ... }`
    Struct { fields: Vec<FfiField> },
    /// `union Foo { ... }`
    Union { fields: Vec<FfiField> },
    /// `enum Foo { ... }`
    Enum { variants: Vec<FfiEnumVariant> },
    /// `type Foo = ...`
    Alias { target: FfiTypeRef },
}

/// A field in a composite type.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiField {
    /// Field name, if named.
    pub name: Option<String>,
    /// Field type.
    pub ty: FfiTypeRef,
}

/// An enum variant.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FfiEnumVariant {
    /// Variant name.
    pub name: String,
    /// Variant fields.
    pub fields: Vec<FfiField>,
}

/// A Rust type as seen at the FFI boundary.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FfiTypeRef {
    /// `()`
    Unit,
    /// Primitive scalar or standard C scalar alias.
    Primitive(String),
    /// Named type path.
    Named(String),
    /// `*const T` or `*mut T`
    RawPointer {
        mutable: bool,
        inner: Box<FfiTypeRef>,
    },
    /// `&T` or `&mut T`
    Reference {
        mutable: bool,
        lifetime: Option<String>,
        inner: Box<FfiTypeRef>,
    },
    /// `[T; N]`
    Array { inner: Box<FfiTypeRef>, len: String },
    /// `[T]`
    Slice(Box<FfiTypeRef>),
    /// `(T1, T2, ...)`
    Tuple(Vec<FfiTypeRef>),
    /// `extern "C" fn(...) -> ...`
    BareFunction {
        abi: String,
        inputs: Vec<FfiTypeRef>,
        output: Option<Box<FfiTypeRef>>,
    },
    /// Any other Rust-only or currently unsupported type syntax.
    Unsupported(String),
}

impl FfiTypeRef {
    pub(crate) fn display_name(&self) -> String {
        match self {
            Self::Unit => "()".to_string(),
            Self::Primitive(name) | Self::Named(name) | Self::Unsupported(name) => name.clone(),
            Self::RawPointer { mutable, inner } => {
                let qualifier = if *mutable { "mut" } else { "const" };
                format!("*{qualifier} {}", inner.display_name())
            }
            Self::Reference {
                mutable,
                lifetime,
                inner,
            } => match (mutable, lifetime.as_deref()) {
                (true, Some(lifetime)) => format!("&{lifetime} mut {}", inner.display_name()),
                (false, Some(lifetime)) => format!("&{lifetime} {}", inner.display_name()),
                (true, None) => format!("&mut {}", inner.display_name()),
                (false, None) => format!("&{}", inner.display_name()),
            },
            Self::Array { inner, len } => format!("[{}; {len}]", inner.display_name()),
            Self::Slice(inner) => format!("[{}]", inner.display_name()),
            Self::Tuple(items) => {
                let rendered = items
                    .iter()
                    .map(FfiTypeRef::display_name)
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("({rendered})")
            }
            Self::BareFunction {
                abi,
                inputs,
                output,
            } => {
                let rendered_inputs = inputs
                    .iter()
                    .map(FfiTypeRef::display_name)
                    .collect::<Vec<_>>()
                    .join(", ");
                match output {
                    Some(output) => format!(
                        "extern \"{abi}\" fn({rendered_inputs}) -> {}",
                        output.display_name()
                    ),
                    None => format!("extern \"{abi}\" fn({rendered_inputs})"),
                }
            }
        }
    }
}
