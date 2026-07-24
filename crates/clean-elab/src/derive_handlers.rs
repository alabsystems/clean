// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Built-in derive handlers for common typeclasses.
//!
//! Provides derive handlers for:
//! - [`DeriveBEq`] — boolean equality by structural comparison
//! - [`DeriveRepr`] — string representation
//! - [`DeriveHashable`] — hashing by constructor tag + fields
//! - [`DeriveInhabited`] — default inhabitant from first constructor
//! - [`DeriveDecidableEq`] — decidable equality by structural comparison
//!
//! Each handler enumerates the constructors of an [`InductiveVal`], builds
//! the instance body as an [`Expr`] tree, and returns a
//! [`Declaration::Definition`].

use clean_kernel::{
    BinderInfo, ConstructorVal, Declaration, Environment, Expr, ExprKind, InductiveVal, Level, Name,
};

use crate::derive::{instance_name, DeriveError, DeriveHandler};
use crate::ElabError;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Route the legacy public handler types through the single maintained batch-2
/// implementation and its automatic-derive admission gate. This removes the
/// former duplicate constant/sorry fallbacks while preserving the public API.
fn derive_via_batch2(
    handler: Box<dyn crate::derive_ext_handlers2::ExtDeriveHandler2>,
    ind: &InductiveVal,
    env: &Environment,
) -> Result<Vec<Declaration>, DeriveError> {
    reject_complex_inductive(ind, handler.class_name())?;
    crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(handler).derive(ind, env)
}

/// Look up all constructors for an inductive type, returning them in order.
pub(crate) fn lookup_constructors(
    ind: &InductiveVal,
    env: &Environment,
) -> Result<Vec<ConstructorVal>, DeriveError> {
    ind.constructor_names
        .iter()
        .map(|name| {
            env.get_constructor(name)
                .cloned()
                .ok_or_else(|| DeriveError::ConstructorNotFound(name.to_string()))
        })
        .collect()
}

/// Check that the inductive is not recursive or reflexive (unsupported for
/// simple structural derivations).
pub(crate) fn reject_complex_inductive(
    ind: &InductiveVal,
    class_name: &str,
) -> Result<(), DeriveError> {
    if ind.is_reflexive || ind.is_recursive {
        return Err(DeriveError::Unsupported {
            class_name: class_name.to_owned(),
            ind_name: ind.name.to_string(),
            reason: "recursive or reflexive inductive types are not supported".to_owned(),
        });
    }
    Ok(())
}

/// Build `Bool.true` constant expression.
pub(crate) fn mk_bool_true() -> Expr {
    Expr::const_str("Bool.true")
}

/// Build `Bool.false` constant expression.
pub(crate) fn mk_bool_false() -> Expr {
    Expr::const_str("Bool.false")
}

/// Build `Bool` type expression.
pub(crate) fn mk_bool() -> Expr {
    Expr::const_str("Bool")
}

/// Build a string literal expression.
pub(crate) fn mk_str_lit(s: &str) -> Expr {
    Expr::str_lit(s)
}

/// Build `Nat` type expression.
pub(crate) fn mk_nat() -> Expr {
    Expr::const_str("Nat")
}

/// Narrow ABI for `@[derive_handler]` declarations.
///
/// A handler must be a constant whose type ends in `Class α`, where `α` is one
/// of the handler's bound variables. The elaborator instantiates that target
/// binder with the type currently being derived and preserves any remaining
/// binders as the derived instance's parameters/constraints.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct UserDeriveHandlerShape {
    pub(crate) class_name: Name,
    pub(crate) binder_count: usize,
    pub(crate) target_bvar_idx: u32,
}

/// Extract the supported `@[derive_handler]` shape from a declaration type.
#[must_use]
pub(crate) fn user_derive_handler_shape(ty: &Expr) -> Option<UserDeriveHandlerShape> {
    let mut binder_count = 0usize;
    let mut curr = ty;
    while let ExprKind::Pi(_, _, body) = curr.kind() {
        binder_count += 1;
        curr = body.as_ref();
    }

    let mut args = curr.get_app_args();
    if args.len() != 1 {
        return None;
    }

    let ExprKind::Const(class_name, _) = curr.get_app_fn().kind() else {
        return None;
    };
    let target = args.pop()?;
    let ExprKind::BVar(target_bvar_idx) = target.kind() else {
        return None;
    };
    let target_bvar_idx = *target_bvar_idx;
    if usize::try_from(target_bvar_idx).ok()? >= binder_count {
        return None;
    }

    Some(UserDeriveHandlerShape {
        class_name: class_name.clone(),
        binder_count,
        target_bvar_idx,
    })
}

/// Register a user-defined derive handler declaration in the environment.
pub fn register_user_derive_handler(
    env: &mut Environment,
    decl_name: &Name,
) -> Result<Name, ElabError> {
    let const_info = env
        .get_const(decl_name)
        .ok_or_else(|| ElabError::UnknownIdent(format!("derive handler '{decl_name}'")))?;
    let shape = user_derive_handler_shape(&const_info.type_).ok_or_else(|| ElabError::Unsupported {
        feature: format!(
            "@[derive_handler] on '{}' requires a type ending in `Class α` for a bound target parameter",
            decl_name
        ),
    })?;
    env.register_derive_handler(shape.class_name.clone(), decl_name.clone());
    Ok(shape.class_name)
}

/// Build the inductive type applied to its parameters as bvars.
///
/// If the type has `n` params, returns `T.{u...} bvar(n-1) bvar(n-2) ... bvar(0)`.
/// Universe level params are propagated from the inductive's `level_params`.
pub(crate) fn mk_ind_type_applied(ind: &InductiveVal) -> Expr {
    let levels: Vec<Level> = ind
        .level_params
        .iter()
        .map(|name| Level::param(name.clone()))
        .collect();
    let base = Expr::const_(ind.name.clone(), levels);
    let n = ind.num_params;
    if n == 0 {
        return base;
    }
    let args: Vec<Expr> = (0..n).rev().map(Expr::bvar).collect();
    Expr::apps(base, args)
}

/// Wrap an expression in `num_params` lambda binders for the type parameters.
///
/// Each parameter gets a `Sort(1)` (Type) binder type as a simplification.
pub(crate) fn wrap_param_lambdas(body: Expr, num_params: u32) -> Expr {
    let mut result = body;
    for _ in 0..num_params {
        result = Expr::lam(
            BinderInfo::Default,
            Expr::sort(Level::succ(Level::zero())),
            result,
        );
    }
    result
}

/// Build the instance type: `ClassName IndType` (applied to params).
pub(crate) fn mk_instance_type(class_name: &str, ind: &InductiveVal) -> Expr {
    let ind_applied = mk_ind_type_applied(ind);
    Expr::app(Expr::const_str(class_name), ind_applied)
}

/// Extract the universe level from an inductive type's type expression.
///
/// For `Sort(l)`, returns `l`. For `Pi(_, _, body)`, recurses into the body
/// (strips binders for parameterized types). Falls back to `Succ(Zero)` (Type 0).
pub(crate) fn extract_universe_level(ty: &Expr) -> Level {
    match ty.kind() {
        ExprKind::Sort(l) => l.clone(),
        ExprKind::Pi(_, _, body) => extract_universe_level(body),
        _ => Level::succ(Level::zero()),
    }
}

/// Compute the universe level for an inductive's instances.
///
/// Uses the inductive's `type_` to extract the sort level. For `Nat : Type 0`,
/// this returns `Succ(Zero)`. For `List.{u} : Type u → Type u`, with level
/// params `[u]`, this returns `Param(u)`.
pub(crate) fn ind_universe_level(ind: &InductiveVal) -> Level {
    extract_universe_level(&ind.type_)
}

/// Wrap an expression type in `num_params` pi binders (forall) for type params.
pub(crate) fn wrap_param_pis(body: Expr, num_params: u32) -> Expr {
    let mut result = body;
    for _ in 0..num_params {
        result = Expr::pi(
            BinderInfo::Implicit,
            Expr::sort(Level::succ(Level::zero())),
            result,
        );
    }
    result
}

// ---------------------------------------------------------------------------
// DeriveBEq
// ---------------------------------------------------------------------------

/// Derive handler for `BEq` — boolean equality by structural comparison.
///
/// For each pair of constructors:
/// - Same constructor: compare fields pairwise with `&&`
/// - Different constructors: return `false`
pub struct DeriveBEq;

impl DeriveHandler for DeriveBEq {
    fn class_name(&self) -> &str {
        "BEq"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        derive_via_batch2(Box::new(crate::derive_ext_handlers2::DeriveBEq2), ind, env)
    }
}

// ---------------------------------------------------------------------------
// DeriveRepr
// ---------------------------------------------------------------------------

/// Derive handler for `Repr` — string representation.
///
/// Generates a `reprPrec` function that prints the constructor name
/// followed by field representations.
pub struct DeriveRepr;

impl DeriveHandler for DeriveRepr {
    fn class_name(&self) -> &str {
        "Repr"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        derive_via_batch2(Box::new(crate::derive_ext_handlers2::DeriveRepr2), ind, env)
    }
}

// ---------------------------------------------------------------------------
// DeriveHashable
// ---------------------------------------------------------------------------

/// Derive handler for `Hashable` — hash by constructor tag + fields.
///
/// Generates a `hash` function that mixes the constructor index with
/// field hashes.
pub struct DeriveHashable;

impl DeriveHandler for DeriveHashable {
    fn class_name(&self) -> &str {
        "Hashable"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        derive_via_batch2(
            Box::new(crate::derive_ext_handlers2::DeriveHashable2),
            ind,
            env,
        )
    }
}

// ---------------------------------------------------------------------------
// DeriveInhabited
// ---------------------------------------------------------------------------

/// Derive handler for `Inhabited` from a closed nullary constructor.
pub struct DeriveInhabited;

impl DeriveHandler for DeriveInhabited {
    fn class_name(&self) -> &str {
        "Inhabited"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        let ctors = lookup_constructors(ind, env)?;

        if ctors.is_empty() {
            return Err(DeriveError::Unsupported {
                class_name: "Inhabited".to_owned(),
                ind_name: ind.name.to_string(),
                reason: "type has no constructors".to_owned(),
            });
        }

        if ind.num_params != 0 {
            return Err(DeriveError::Unsupported {
                class_name: "Inhabited".to_owned(),
                ind_name: ind.name.to_string(),
                reason: "parameter instances are not synthesized by this handler".to_owned(),
            });
        }

        // Use the first constructor only when it is already a closed value.
        // Applying an untyped `Inhabited.default` constant to every field was
        // not instance synthesis and could create malformed generated terms.
        let first_ctor = &ctors[0];
        if first_ctor.num_fields != 0 {
            return Err(DeriveError::Unsupported {
                class_name: "Inhabited".to_owned(),
                ind_name: ind.name.to_string(),
                reason: "first constructor has fields; field Inhabited instances are not \
                         synthesized by this handler"
                    .to_owned(),
            });
        }
        let ind_levels: Vec<Level> = ind
            .level_params
            .iter()
            .map(|name| Level::param(name.clone()))
            .collect();
        let default_val = Expr::const_(first_ctor.name.clone(), ind_levels);
        let ind_ty = mk_ind_type_applied(ind);
        let u_level = ind_universe_level(ind);

        let inst_name = instance_name("Inhabited", &ind.name);
        let inst_ty = Expr::app(
            Expr::const_str_levels("Inhabited", vec![u_level.clone()]),
            ind_ty.clone(),
        );
        let inst_val = Expr::apps(
            Expr::const_str_levels("Inhabited.mk", vec![u_level]),
            [ind_ty, default_val],
        );

        Ok(vec![Declaration::Definition {
            name: inst_name,
            level_params: ind.level_params.clone(),
            type_: inst_ty,
            value: inst_val,
            is_reducible: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveDecidableEq
// ---------------------------------------------------------------------------

/// Derive handler for `DecidableEq` — decidable equality.
///
/// Generates a function producing `Decidable (a = b)` for each pair of
/// values by structural comparison. Same-constructor pairs compare fields;
/// different-constructor pairs return `isFalse`.
pub struct DeriveDecidableEq;

impl DeriveHandler for DeriveDecidableEq {
    fn class_name(&self) -> &str {
        "DecidableEq"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        derive_via_batch2(
            Box::new(crate::derive_ext_handlers2::DeriveDecidableEq2),
            ind,
            env,
        )
    }
}

// ---------------------------------------------------------------------------
// DeriveNonempty
// ---------------------------------------------------------------------------

/// Derive handler for `Nonempty` — a constructive proof of nonemptiness.
///
/// `Nonempty α : Prop` witnesses that `α` is inhabited. For an inductive whose
/// first constructor is nullary (takes no fields), the constructor itself is a
/// closed witness, so the instance value is `Nonempty.intro T C`. This term is
/// fully kernel-checkable and introduces no `sorry`/axioms.
///
/// Constructors with fields are rejected with [`DeriveError::Unsupported`]
/// rather than emitting an unchecked placeholder term: building a witness for
/// such a constructor would require `Inhabited` (or other) instances for each
/// field, which are not available structurally here. Refusing keeps every
/// generated `Nonempty` instance sound.
pub struct DeriveNonempty;

impl DeriveHandler for DeriveNonempty {
    fn class_name(&self) -> &str {
        "Nonempty"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        let ctors = lookup_constructors(ind, env)?;

        let first_ctor = ctors.first().ok_or_else(|| DeriveError::Unsupported {
            class_name: "Nonempty".to_owned(),
            ind_name: ind.name.to_string(),
            reason: "type has no constructors".to_owned(),
        })?;

        if ind.num_params != 0 {
            return Err(DeriveError::Unsupported {
                class_name: "Nonempty".to_owned(),
                ind_name: ind.name.to_string(),
                reason: "parameter witnesses are not synthesized by this handler".to_owned(),
            });
        }

        if first_ctor.num_fields != 0 {
            return Err(DeriveError::Unsupported {
                class_name: "Nonempty".to_owned(),
                ind_name: ind.name.to_string(),
                reason: "first constructor has fields; a closed witness cannot be \
                         synthesized without field instances"
                    .to_owned(),
            });
        }

        let u_level = ind_universe_level(ind);
        let ind_ty = mk_ind_type_applied(ind);

        // Witness is the nullary constructor constant, carrying the inductive's
        // own level params.
        let ind_levels: Vec<Level> = ind
            .level_params
            .iter()
            .map(|name| Level::param(name.clone()))
            .collect();
        let witness = Expr::const_(first_ctor.name.clone(), ind_levels);

        // Nonempty.intro.{u} : ∀ (α : Sort u), α → Nonempty α  (α is explicit).
        let proof = Expr::apps(
            Expr::const_str_levels("Nonempty.intro", vec![u_level.clone()]),
            [ind_ty.clone(), witness],
        );
        let proof = wrap_param_lambdas(proof, ind.num_params);

        // Nonempty.{u} T : Prop
        let inst_ty = Expr::app(Expr::const_str_levels("Nonempty", vec![u_level]), ind_ty);
        let inst_ty = wrap_param_pis(inst_ty, ind.num_params);

        Ok(vec![Declaration::Definition {
            name: instance_name("Nonempty", &ind.name),
            level_params: ind.level_params.clone(),
            type_: inst_ty,
            value: proof,
            is_reducible: true,
        }])
    }
}

// ---------------------------------------------------------------------------
// DeriveSizeOf
// ---------------------------------------------------------------------------

/// Derive handler for `SizeOf` — a structural size measure.
///
/// `SizeOf α` provides `sizeOf : α → Nat`. Until a structural recursor
/// implementation is available, this handler fails closed instead of reporting
/// the former constant-zero placeholder as a successful derivation.
pub struct DeriveSizeOf;

impl DeriveHandler for DeriveSizeOf {
    fn class_name(&self) -> &str {
        "SizeOf"
    }

    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError> {
        let _ = lookup_constructors(ind, env)?;
        Err(DeriveError::Unsupported {
            class_name: "SizeOf".to_owned(),
            ind_name: ind.name.to_string(),
            reason: "no structural SizeOf construction is available".to_owned(),
        })
    }
}

// ---------------------------------------------------------------------------
// Registration helper
// ---------------------------------------------------------------------------

/// Register all built-in derive handlers in the given registry.
pub fn register_builtin_handlers(registry: &mut crate::derive::DeriveRegistry) {
    // The original first-generation handlers below remain useful as small
    // construction examples, but their BEq/Repr/Hashable/DecidableEq bodies are
    // intentionally incomplete (constant equality/representation/hash or a
    // sorry-backed decision procedure). Canonical automatic deriving must use
    // the genuine batch-2 constructors and the shared fail-closed adapter.
    registry.register_handler(
        "BEq",
        Box::new(crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(
            Box::new(crate::derive_ext_handlers2::DeriveBEq2),
        )),
    );
    registry.register_handler(
        "Repr",
        Box::new(crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(
            Box::new(crate::derive_ext_handlers2::DeriveRepr2),
        )),
    );
    registry.register_handler(
        "Hashable",
        Box::new(crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(
            Box::new(crate::derive_ext_handlers2::DeriveHashable2),
        )),
    );
    registry.register_handler("Inhabited", Box::new(DeriveInhabited));
    registry.register_handler(
        "DecidableEq",
        Box::new(crate::derive_handlers_ext::ExtDeriveHandler2Adapter::new(
            Box::new(crate::derive_ext_handlers2::DeriveDecidableEq2),
        )),
    );
}
