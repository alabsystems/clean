// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Extended derive handler registry with batch derivation support.
//!
//! Provides [`DeriveHandlerRegistry`] for batch derivation of multiple
//! typeclasses from a single inductive type. Handlers implement
//! [`ExtDeriveHandler`] operating on pre-extracted [`ConstructorInfo`]
//! slices rather than requiring full environment access.
//!
//! Built-in handlers: BEq, Hashable, Repr, Ord, Inhabited, DecidableEq.

use std::collections::HashMap;

use clean_kernel::{BinderInfo, Expr, Level, Name};

use crate::derive::DeriveError;
use crate::derive_handlers::{mk_bool_true, wrap_param_lambdas, wrap_param_pis};

// ---------------------------------------------------------------------------
// Core types
// ---------------------------------------------------------------------------

/// Information about a single constructor of an inductive type.
#[derive(Debug, Clone)]
pub(crate) struct ConstructorInfo {
    /// Fully qualified constructor name (e.g., `Color.Red`).
    pub(crate) name: Name,
    /// Fields: (field_name, field_type). Empty for enum-like constructors.
    pub(crate) fields: Vec<(Name, Expr)>,
    /// Whether this constructor references the inductive type being defined.
    pub(crate) is_recursive: bool,
}

/// A derived declaration ready for registration.
#[derive(Debug, Clone)]
// Staged Lean4-parity scaffold with no caller yet (tests included): kept per the
// keep-and-annotate doctrine — see docs/AUDIT_LEAN4_REPLACEMENT_2026-07-22.md (dated 2026-07-30).
#[allow(dead_code)]
pub(crate) struct DerivedDecl {
    pub(crate) name: Name,
    pub(crate) type_: Expr,
    pub(crate) value: Expr,
    pub(crate) is_instance: bool,
}

/// Trait for extended derive handlers operating on constructor metadata.
pub(crate) trait ExtDeriveHandler: Send + Sync {
    fn derive(
        &self,
        type_name: &Name,
        type_expr: &Expr,
        ctors: &[ConstructorInfo],
        _num_params: u32,
        level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError>;

    fn class_name(&self) -> &str;
}

// ---------------------------------------------------------------------------
// Registry
// ---------------------------------------------------------------------------

/// Registry of extended derive handlers with batch derivation.
pub(crate) struct DeriveHandlerRegistry {
    handlers: HashMap<String, Box<dyn ExtDeriveHandler>>,
}

impl DeriveHandlerRegistry {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    pub(crate) fn register(&mut self, class_name: Name, handler: Box<dyn ExtDeriveHandler>) {
        self.handlers.insert(class_name.to_string(), handler);
    }

    #[must_use]
    pub(crate) fn has_handler(&self, class_name: &str) -> bool {
        self.handlers.contains_key(class_name)
    }

    /// Derive instances for all requested classes in one batch.
    pub(crate) fn derive_all(
        &self,
        type_name: &Name,
        type_expr: &Expr,
        ctors: &[ConstructorInfo],
        classes: &[Name],
        num_params: u32,
        level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError> {
        let mut results = Vec::new();
        for class in classes {
            let class_str = class.to_string();
            let handler = self
                .handlers
                .get(&class_str)
                .ok_or(DeriveError::NoHandler(class_str))?;
            results.extend(handler.derive(
                type_name,
                type_expr,
                ctors,
                num_params,
                level_params,
            )?);
        }
        Ok(results)
    }

    /// Return a registry pre-populated with all 6 built-in handlers.
    #[must_use]
    pub(crate) fn default_registry() -> Self {
        let mut reg = Self::new();
        reg.register(Name::from_string("BEq"), Box::new(DeriveBEqExt));
        reg.register(Name::from_string("Hashable"), Box::new(DeriveHashableExt));
        reg.register(Name::from_string("Repr"), Box::new(DeriveReprExt));
        reg.register(Name::from_string("Ord"), Box::new(DeriveOrdExt));
        reg.register(Name::from_string("Inhabited"), Box::new(DeriveInhabitedExt));
        reg.register(
            Name::from_string("DecidableEq"),
            Box::new(DeriveDecidableEqExt),
        );
        reg
    }

    pub(crate) fn registered_classes(&self) -> Vec<&str> {
        self.handlers.keys().map(String::as_str).collect()
    }
}

impl std::fmt::Debug for DeriveHandlerRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeriveHandlerRegistry")
            .field("handlers", &self.handlers.keys().collect::<Vec<_>>())
            .finish()
    }
}

// ---------------------------------------------------------------------------
// Shared helpers
// ---------------------------------------------------------------------------

fn ext_instance_name(class_name: &str, type_name: &Name) -> Name {
    Name::from_string(&format!("inst{class_name}{type_name}"))
}

fn mk_applied_type(type_name: &Name, num_params: u32) -> Expr {
    let base = Expr::const_(type_name.clone(), vec![]);
    if num_params == 0 {
        return base;
    }
    let args: Vec<Expr> = (0..num_params).rev().map(Expr::bvar).collect();
    Expr::apps(base, args)
}

fn reject_recursive(
    ctors: &[ConstructorInfo],
    class_name: &str,
    type_name: &Name,
) -> Result<(), DeriveError> {
    if ctors.iter().any(|c| c.is_recursive) {
        return Err(DeriveError::Unsupported {
            class_name: class_name.to_owned(),
            ind_name: type_name.to_string(),
            reason: "recursive constructors are not supported by this handler".to_owned(),
        });
    }
    Ok(())
}

fn wrap_params(value: Expr, type_: Expr, num_params: u32) -> (Expr, Expr) {
    (
        wrap_param_lambdas(value, num_params),
        wrap_param_pis(type_, num_params),
    )
}

fn mk_instance_type_for(type_name: &Name, class_name: &str, num_params: u32) -> Expr {
    Expr::app(
        Expr::const_str(class_name),
        mk_applied_type(type_name, num_params),
    )
}

/// Build a two-argument lambda: `fun (a : ty) (b : ty) => body`.
fn mk_binary_lam(ty: &Expr, body: Expr) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        ty.clone(),
        Expr::lam(BinderInfo::Default, ty.clone(), body),
    )
}

// ---------------------------------------------------------------------------
// DeriveBEqExt
// ---------------------------------------------------------------------------

/// Derive `BEq` by structural comparison of constructor fields.
pub(crate) struct DeriveBEqExt;

impl ExtDeriveHandler for DeriveBEqExt {
    fn class_name(&self) -> &str {
        "BEq"
    }

    fn derive(
        &self,
        type_name: &Name,
        _type_expr: &Expr,
        ctors: &[ConstructorInfo],
        num_params: u32,
        _level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError> {
        reject_recursive(ctors, "BEq", type_name)?;
        let ind_ty = mk_applied_type(type_name, num_params);
        if !(ctors.is_empty() || (ctors.len() == 1 && ctors[0].fields.is_empty())) {
            return Err(DeriveError::Unsupported {
                class_name: "BEq".to_owned(),
                ind_name: type_name.to_string(),
                reason: "this legacy handler only has exact equality for an empty or \
                         singleton-nullary type"
                    .to_owned(),
            });
        }
        let body = mk_bool_true();
        let beq_fn = mk_binary_lam(&ind_ty, body);
        let inst_body = Expr::app(Expr::const_str("BEq.mk"), beq_fn);
        let (value, type_) = wrap_params(
            inst_body,
            mk_instance_type_for(type_name, "BEq", num_params),
            num_params,
        );
        Ok(vec![DerivedDecl {
            name: ext_instance_name("BEq", type_name),
            type_,
            value,
            is_instance: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveHashableExt
// ---------------------------------------------------------------------------

/// Derive `Hashable` by hashing constructor tag + fields.
pub(crate) struct DeriveHashableExt;

impl ExtDeriveHandler for DeriveHashableExt {
    fn class_name(&self) -> &str {
        "Hashable"
    }

    fn derive(
        &self,
        type_name: &Name,
        _type_expr: &Expr,
        ctors: &[ConstructorInfo],
        _num_params: u32,
        _level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError> {
        reject_recursive(ctors, "Hashable", type_name)?;
        Err(DeriveError::Unsupported {
            class_name: "Hashable".to_owned(),
            ind_name: type_name.to_string(),
            reason: "this legacy handler has no structural hash construction".to_owned(),
        })
    }
}

// ---------------------------------------------------------------------------
// DeriveReprExt
// ---------------------------------------------------------------------------

/// Derive `Repr` by pretty-printing constructor name + fields.
pub(crate) struct DeriveReprExt;

impl ExtDeriveHandler for DeriveReprExt {
    fn class_name(&self) -> &str {
        "Repr"
    }

    fn derive(
        &self,
        type_name: &Name,
        _type_expr: &Expr,
        _ctors: &[ConstructorInfo],
        _num_params: u32,
        _level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError> {
        Err(DeriveError::Unsupported {
            class_name: "Repr".to_owned(),
            ind_name: type_name.to_string(),
            reason: "this legacy handler has no constructor-sensitive representation".to_owned(),
        })
    }
}

// ---------------------------------------------------------------------------
// DeriveOrdExt
// ---------------------------------------------------------------------------

/// Derive `Ord` by lexicographic comparison of constructor tags then fields.
pub(crate) struct DeriveOrdExt;

impl ExtDeriveHandler for DeriveOrdExt {
    fn class_name(&self) -> &str {
        "Ord"
    }

    fn derive(
        &self,
        type_name: &Name,
        _type_expr: &Expr,
        ctors: &[ConstructorInfo],
        num_params: u32,
        level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError> {
        reject_recursive(ctors, "Ord", type_name)?;
        if num_params != 0 || !level_params.is_empty() || !ctors.is_empty() {
            return Err(DeriveError::Unsupported {
                class_name: "Ord".to_owned(),
                ind_name: type_name.to_string(),
                reason: "this legacy handler only supports a monomorphic empty type".to_owned(),
            });
        }
        let ind_ty = Expr::const_(type_name.clone(), vec![]);
        let compare_body = Expr::const_(Name::from_string("Ordering.eq"), vec![]);
        let compare_fn = mk_binary_lam(&ind_ty, compare_body);
        let type_ = Expr::app(
            Expr::const_str_levels("Ord", vec![Level::zero()]),
            ind_ty.clone(),
        );
        let value = Expr::apps(
            Expr::const_str_levels("Ord.mk", vec![Level::zero()]),
            [ind_ty, compare_fn],
        );
        Ok(vec![DerivedDecl {
            name: ext_instance_name("Ord", type_name),
            type_,
            value,
            is_instance: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveInhabitedExt
// ---------------------------------------------------------------------------

/// Derive `Inhabited` from the first constructor.
pub(crate) struct DeriveInhabitedExt;

impl ExtDeriveHandler for DeriveInhabitedExt {
    fn class_name(&self) -> &str {
        "Inhabited"
    }

    fn derive(
        &self,
        type_name: &Name,
        _type_expr: &Expr,
        ctors: &[ConstructorInfo],
        num_params: u32,
        level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError> {
        let first_ctor = ctors.first().ok_or_else(|| DeriveError::Unsupported {
            class_name: "Inhabited".to_owned(),
            ind_name: type_name.to_string(),
            reason: "type has no constructors".to_owned(),
        })?;
        if num_params != 0 || !level_params.is_empty() || !first_ctor.fields.is_empty() {
            return Err(DeriveError::Unsupported {
                class_name: "Inhabited".to_owned(),
                ind_name: type_name.to_string(),
                reason: "a closed nullary constructor is required; parameter and field \
                         instances are not synthesized by this handler"
                    .to_owned(),
            });
        }
        let u = Level::succ(Level::zero());
        let ind_ty = Expr::const_(type_name.clone(), vec![]);
        let default_val = Expr::const_(first_ctor.name.clone(), vec![]);
        let type_ = Expr::app(
            Expr::const_str_levels("Inhabited", vec![u.clone()]),
            ind_ty.clone(),
        );
        let value = Expr::apps(
            Expr::const_str_levels("Inhabited.mk", vec![u]),
            [ind_ty, default_val],
        );
        Ok(vec![DerivedDecl {
            name: ext_instance_name("Inhabited", type_name),
            type_,
            value,
            is_instance: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveDecidableEqExt
// ---------------------------------------------------------------------------

/// Derive `DecidableEq` from field-wise decidability.
pub(crate) struct DeriveDecidableEqExt;

impl ExtDeriveHandler for DeriveDecidableEqExt {
    fn class_name(&self) -> &str {
        "DecidableEq"
    }

    fn derive(
        &self,
        type_name: &Name,
        _type_expr: &Expr,
        ctors: &[ConstructorInfo],
        _num_params: u32,
        _level_params: &[Name],
    ) -> Result<Vec<DerivedDecl>, DeriveError> {
        reject_recursive(ctors, "DecidableEq", type_name)?;
        Err(DeriveError::Unsupported {
            class_name: "DecidableEq".to_owned(),
            ind_name: type_name.to_string(),
            reason: "this legacy handler has no proof-producing equality decision procedure"
                .to_owned(),
        })
    }
}

// ---------------------------------------------------------------------------
// Constructor extraction from InductiveVal
// ---------------------------------------------------------------------------

/// Extract [`ConstructorInfo`] list from a kernel `InductiveVal` and env.
pub(crate) fn extract_constructor_info(
    ind: &clean_kernel::InductiveVal,
    env: &clean_kernel::Environment,
) -> Result<Vec<ConstructorInfo>, DeriveError> {
    ind.constructor_names
        .iter()
        .map(|ctor_name| {
            let ctor_val = env
                .get_constructor(ctor_name)
                .ok_or_else(|| DeriveError::ConstructorNotFound(ctor_name.to_string()))?;

            let mut current = &ctor_val.type_;
            for _ in 0..ctor_val.num_params {
                if let clean_kernel::ExprKind::Pi(_, _, body) = current.kind() {
                    current = body.as_ref();
                }
            }

            let mut fields = Vec::new();
            let mut field_idx = 0u32;
            while let clean_kernel::ExprKind::Pi(_, domain, body) = current.kind() {
                fields.push((
                    Name::from_string(&format!("field{field_idx}")),
                    (**domain).clone(),
                ));
                current = body.as_ref();
                field_idx += 1;
            }

            let is_recursive = fields
                .iter()
                .any(|(_, ty)| contains_name_ref(ty, &ind.name));

            Ok(ConstructorInfo {
                name: ctor_name.clone(),
                fields,
                is_recursive,
            })
        })
        .collect()
}

/// Check if an expression contains a reference to `name` (shallow).
fn contains_name_ref(expr: &Expr, name: &Name) -> bool {
    match expr.kind() {
        clean_kernel::ExprKind::Const(n, _) => n == name,
        clean_kernel::ExprKind::App(f, a) => {
            contains_name_ref(f, name) || contains_name_ref(a, name)
        }
        clean_kernel::ExprKind::Pi(_, d, b) | clean_kernel::ExprKind::Lam(_, d, b) => {
            contains_name_ref(d, name) || contains_name_ref(b, name)
        }
        _ => false,
    }
}
