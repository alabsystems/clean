// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended derive handler module for higher-kinded and metaprogramming typeclasses.
//!
//! Provides derive handlers for:
//! - [`DeriveFunctor`] — `Functor` instance with `map` function
//! - [`DeriveTraversable`] — `Traversable` instance with `traverse`
//! - [`DeriveFoldable`] — `Foldable` instance with `foldr`
//! - [`DeriveNonempty`] — proof of nonemptiness from constructor existence
//! - [`DeriveSizeOf`] — `SizeOf` instance for runtime memory analysis
//! - [`DeriveToExpr`] — `ToExpr` instance for meta-programming reflection
//! - [`DeriveFromExpr`] — `FromExpr` instance for parsing kernel `Expr` back
//! - Custom derive handler registration via [`DeriveExt2Config`]
//! - Result caching via [`DeriveExt2Cache`]

use std::collections::HashMap;

use clean_kernel::{Expr, Level, Name};

use crate::derive::DeriveError;

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Enumeration of derive classes supported by this module.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum DeriveClass {
    Functor,
    Traversable,
    Foldable,
    Nonempty,
    SizeOf,
    ToExpr,
    FromExpr,
    Custom(String),
}

impl DeriveClass {
    pub(crate) fn class_name(&self) -> &str {
        match self {
            Self::Functor => "Functor",
            Self::Traversable => "Traversable",
            Self::Foldable => "Foldable",
            Self::Nonempty => "Nonempty",
            Self::SizeOf => "SizeOf",
            Self::ToExpr => "ToExpr",
            Self::FromExpr => "FromExpr",
            Self::Custom(s) => s.as_str(),
        }
    }
}

/// Constructor metadata for the ext2 derive pipeline.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Ext2ConstructorInfo {
    pub(crate) name: Name,
    pub(crate) fields: Vec<(Name, Expr)>,
    pub(crate) is_recursive: bool,
}

/// Input to an ext2 derive handler.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct DeriveExt2Input {
    pub(crate) type_name: Name,
    pub(crate) type_expr: Expr,
    pub(crate) constructors: Vec<Ext2ConstructorInfo>,
    pub(crate) num_params: u32,
    pub(crate) level_params: Vec<Name>,
    pub(crate) target_class: DeriveClass,
}

/// Output from an ext2 derive handler.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct DeriveExt2Output {
    pub(crate) decl_name: Name,
    pub(crate) decl_type: Expr,
    pub(crate) decl_value: Expr,
    pub(crate) auxiliary_decls: Vec<(Name, Expr, Expr)>,
}

/// Type alias for custom derive handler functions.
pub(crate) type DeriveExt2Handler =
    fn(&DeriveExt2Input, &DeriveExt2Config) -> Result<DeriveExt2Output, DeriveError>;

/// Configuration for the ext2 derive pipeline.
#[derive(Debug, Clone)]
pub(crate) struct DeriveExt2Config {
    pub(crate) enable_caching: bool,
    pub(crate) max_derive_depth: u32,
    pub(crate) custom_handlers: HashMap<String, DeriveExt2Handler>,
}

impl Default for DeriveExt2Config {
    fn default() -> Self {
        Self {
            enable_caching: true,
            max_derive_depth: 16,
            custom_handlers: HashMap::new(),
        }
    }
}

/// Exact cache identity for one ext2 derivation.
///
/// The type name and class alone are not enough: a later declaration can reuse
/// a name with a different telescope or constructors, and custom handler
/// registrations/configuration can change the output for identical input.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct DeriveExt2CacheKey {
    input: DeriveExt2Input,
    max_derive_depth: u32,
    custom_handlers: Vec<(String, usize)>,
}

impl DeriveExt2CacheKey {
    fn new(input: &DeriveExt2Input, config: &DeriveExt2Config) -> Self {
        let mut custom_handlers: Vec<(String, usize)> = config
            .custom_handlers
            .iter()
            .map(|(name, handler)| (name.clone(), *handler as usize))
            .collect();
        custom_handlers.sort_by(|left, right| left.0.cmp(&right.0));
        Self {
            input: input.clone(),
            max_derive_depth: config.max_derive_depth,
            custom_handlers,
        }
    }
}

/// Cache for derived outputs, keyed by the complete input and configuration
/// that can affect handler output.
#[derive(Debug, Clone)]
pub(crate) struct DeriveExt2Cache {
    entries: HashMap<DeriveExt2CacheKey, DeriveExt2Output>,
}

impl DeriveExt2Cache {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    pub(crate) fn lookup(
        &self,
        input: &DeriveExt2Input,
        config: &DeriveExt2Config,
    ) -> Option<&DeriveExt2Output> {
        self.entries.get(&DeriveExt2CacheKey::new(input, config))
    }

    pub(crate) fn insert(
        &mut self,
        input: &DeriveExt2Input,
        config: &DeriveExt2Config,
        output: DeriveExt2Output,
    ) {
        self.entries
            .insert(DeriveExt2CacheKey::new(input, config), output);
    }

    #[must_use]
    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    #[must_use]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

pub(crate) fn ext2_instance_name(class: &DeriveClass, type_name: &Name) -> Name {
    Name::from_string(&format!("inst{}{}", class.class_name(), type_name))
}

fn reject_empty<'a>(
    input: &'a DeriveExt2Input,
    class_name: &str,
) -> Result<&'a Ext2ConstructorInfo, DeriveError> {
    input
        .constructors
        .first()
        .ok_or_else(|| DeriveError::Unsupported {
            class_name: class_name.to_owned(),
            ind_name: input.type_name.to_string(),
            reason: "type has no constructors".to_owned(),
        })
}

// ---------------------------------------------------------------------------
// Derive handlers
// ---------------------------------------------------------------------------

pub(crate) fn derive_functor(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Err(unsupported_shape_error(
        &DeriveClass::Functor,
        &input.type_name,
        "the legacy ext2 pipeline has no variance-aware map construction",
    ))
}

pub(crate) fn derive_traversable(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Err(unsupported_shape_error(
        &DeriveClass::Traversable,
        &input.type_name,
        "the legacy ext2 pipeline has no effectful structural traversal construction",
    ))
}

pub(crate) fn derive_foldable(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Err(unsupported_shape_error(
        &DeriveClass::Foldable,
        &input.type_name,
        "the legacy ext2 pipeline has no structural fold construction",
    ))
}

pub(crate) fn derive_nonempty(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    let first_ctor = reject_empty(input, "Nonempty")?;
    if input.num_params != 0 || !input.level_params.is_empty() || !first_ctor.fields.is_empty() {
        return Err(unsupported_shape_error(
            &DeriveClass::Nonempty,
            &input.type_name,
            "a closed nullary constructor is required; parameter and field witnesses are not synthesized",
        ));
    }
    let u = Level::succ(Level::zero());
    let ind_ty = Expr::const_(input.type_name.clone(), vec![]);
    let witness = Expr::const_(first_ctor.name.clone(), vec![]);
    let value = Expr::apps(
        Expr::const_str_levels("Nonempty.intro", vec![u.clone()]),
        [ind_ty.clone(), witness],
    );
    let type_ = Expr::app(Expr::const_str_levels("Nonempty", vec![u]), ind_ty);

    Ok(DeriveExt2Output {
        decl_name: ext2_instance_name(&DeriveClass::Nonempty, &input.type_name),
        decl_type: type_,
        decl_value: value,
        auxiliary_decls: vec![],
    })
}

pub(crate) fn derive_sizeof(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Err(unsupported_shape_error(
        &DeriveClass::SizeOf,
        &input.type_name,
        "the legacy ext2 pipeline has no structural size construction",
    ))
}

pub(crate) fn derive_to_expr(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Err(unsupported_shape_error(
        &DeriveClass::ToExpr,
        &input.type_name,
        "the legacy ext2 pipeline has no structural expression reflection construction",
    ))
}

pub(crate) fn derive_from_expr(
    input: &DeriveExt2Input,
    _config: &DeriveExt2Config,
) -> Result<DeriveExt2Output, DeriveError> {
    Err(unsupported_shape_error(
        &DeriveClass::FromExpr,
        &input.type_name,
        "the legacy ext2 pipeline has no structural expression parser construction",
    ))
}

// ---------------------------------------------------------------------------
// Registry and dispatch
// ---------------------------------------------------------------------------

/// Main entry point: derive an instance, using cache if enabled.
pub(crate) fn derive_ext2(
    input: &DeriveExt2Input,
    config: &DeriveExt2Config,
    cache: &mut DeriveExt2Cache,
) -> Result<DeriveExt2Output, DeriveError> {
    if config.enable_caching {
        if let Some(cached) = cache.lookup(input, config) {
            return Ok(cached.clone());
        }
    }

    let output = match &input.target_class {
        DeriveClass::Functor => derive_functor(input, config)?,
        DeriveClass::Traversable => derive_traversable(input, config)?,
        DeriveClass::Foldable => derive_foldable(input, config)?,
        DeriveClass::Nonempty => derive_nonempty(input, config)?,
        DeriveClass::SizeOf => derive_sizeof(input, config)?,
        DeriveClass::ToExpr => derive_to_expr(input, config)?,
        DeriveClass::FromExpr => derive_from_expr(input, config)?,
        DeriveClass::Custom(name) => {
            let handler = config
                .custom_handlers
                .get(name)
                .ok_or_else(|| DeriveError::NoHandler(name.clone()))?;
            handler(input, config)?
        }
    };

    if config.enable_caching {
        cache.insert(input, config, output.clone());
    }

    Ok(output)
}

/// Register a custom derive handler in the config.
pub(crate) fn register_custom_handler(
    config: &mut DeriveExt2Config,
    name: &str,
    handler: DeriveExt2Handler,
) {
    config.custom_handlers.insert(name.to_owned(), handler);
}

/// Return all 7 built-in derive classes.
#[must_use]
pub(crate) fn supported_classes() -> Vec<DeriveClass> {
    vec![
        DeriveClass::Functor,
        DeriveClass::Traversable,
        DeriveClass::Foldable,
        DeriveClass::Nonempty,
        DeriveClass::SizeOf,
        DeriveClass::ToExpr,
        DeriveClass::FromExpr,
    ]
}

/// Derive error message for unsupported type shapes.
pub(crate) fn unsupported_shape_error(
    class: &DeriveClass,
    type_name: &Name,
    reason: &str,
) -> DeriveError {
    DeriveError::Unsupported {
        class_name: class.class_name().to_owned(),
        ind_name: type_name.to_string(),
        reason: reason.to_owned(),
    }
}
