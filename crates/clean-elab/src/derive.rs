// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Derive handler framework for automatically generating typeclass instances.
//!
//! Provides a registry of derive handlers that generate typeclass instance
//! declarations from inductive type definitions. This mirrors Lean 4's
//! `@[deriving]` attribute system.
//!
//! # Architecture
//!
//! The [`DeriveRegistry`] stores [`DeriveHandler`] trait objects indexed by
//! typeclass name. When a `deriving` attribute is processed, the registry
//! looks up the handler for the requested class and invokes it with the
//! [`InductiveVal`] to produce instance [`Declaration`]s.
//!
//! # Example
//!
//! ```
//! use clean_elab::derive::{DeriveRegistry, DeriveHandler, DeriveError};
//! use clean_kernel::{InductiveVal, Declaration, Environment};
//!
//! let mut registry = DeriveRegistry::new();
//! assert!(!registry.has_handler("BEq"));
//! ```

use std::collections::{HashMap, HashSet};

use clean_kernel::{
    is_foundational_axiom, BinderInfo, ConstantKind, Declaration, Environment, Expr, ExprKind,
    InductiveVal, Name,
};

/// Errors that can occur during derive handler execution.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum DeriveError {
    /// The requested typeclass has no registered derive handler.
    #[error("no derive handler registered for class `{0}`")]
    NoHandler(String),

    /// The inductive type is not supported by this derive handler.
    #[error("cannot derive `{class_name}` for `{ind_name}`: {reason}")]
    Unsupported {
        class_name: String,
        ind_name: String,
        reason: String,
    },

    /// A constructor lookup failed during derivation.
    #[error("constructor `{0}` not found in environment")]
    ConstructorNotFound(String),

    /// The generated declaration could not be added to the environment.
    #[error("failed to register derived instance `{name}`: {detail}")]
    RegistrationFailed { name: String, detail: String },
}

/// Replace the built-in inductive `Repr` generator's closed bootstrap value
/// with a constructor-aware implementation using a kernel-registered candidate
/// environment.
///
/// Recursive and nested inductives cannot be lowered faithfully from the
/// source constructor list alone: the kernel owns the final recursor packet,
/// auxiliary motives, and constructor field metadata.  The caller therefore
/// registers the completed parent declaration in a cloned environment and
/// invokes this helper before publishing the elaboration result.  No mutation
/// reaches the real environment, and user-defined derive handlers never pass
/// through this built-in-only path.
pub(crate) fn materialize_inductive_repr(
    env: &Environment,
    parent_name: &Name,
    inst: &crate::infer::DerivedInstance,
) -> Result<crate::infer::DerivedInstance, crate::ElabError> {
    let ind = env.get_inductive(parent_name).ok_or_else(|| {
        crate::ElabError::InternalInvariant(format!(
            "cannot materialize Repr before inductive `{parent_name}` is registered"
        ))
    })?;
    if ind.constructor_names.is_empty() {
        return Err(crate::ElabError::Unsupported {
            feature: format!(
                "deriving Repr for empty inductive `{parent_name}` requires an empty eliminator"
            ),
        });
    }

    let (class_levels, target_ty) = match inst.ty.kind() {
        ExprKind::App(class, target) => match class.kind() {
            ExprKind::Const(class_name, levels) if *class_name == Name::from_string("Repr") => {
                (levels.to_vec(), target.as_ref().clone())
            }
            _ => {
                return Err(crate::ElabError::InternalInvariant(format!(
                    "derived Repr instance `{}` has malformed class head: {:?}",
                    inst.name, inst.ty
                )));
            }
        },
        _ => {
            return Err(crate::ElabError::InternalInvariant(format!(
                "derived Repr instance `{}` has malformed type: {:?}",
                inst.name, inst.ty
            )));
        }
    };

    let mut source = format!("fun (value : {parent_name}) (_prec : Nat) => match value with");
    for ctor_name in &ind.constructor_names {
        let ctor = env.get_constructor(ctor_name).ok_or_else(|| {
            crate::ElabError::InternalInvariant(format!(
                "registered inductive `{parent_name}` is missing constructor metadata for `{ctor_name}`"
            ))
        })?;
        let ellipsis = if ctor.num_fields == 0 { "" } else { " .." };
        let rendered_name = format!("{:?}", ctor_name.to_string());
        source.push_str(&format!(" | {ctor_name}{ellipsis} => {rendered_name}"));
    }

    let surface = clean_parser::parse_expr(&source)
        .map_err(|error| crate::ElabError::ParseError(error.to_string()))?;
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let string_ty = Expr::const_(Name::from_string("String"), vec![]);
    let repr_fn_ty = Expr::pi(
        BinderInfo::Default,
        target_ty.clone(),
        Expr::pi(BinderInfo::Default, nat_ty, string_ty),
    );
    let mut ctx = crate::infer::ElabCtx::new(env);
    let repr_fn = ctx.elaborate_with_type(&surface, repr_fn_ty)?;
    let repr_val = Expr::apps(
        Expr::const_(Name::from_string("Repr.mk"), class_levels),
        [target_ty, repr_fn],
    );

    let mut materialized = inst.clone();
    materialized.val = repr_val;
    materialized.level_params =
        crate::infer::collect_level_params(&[&materialized.ty, &materialized.val]);
    Ok(materialized)
}

/// Admit one automatically generated instance at the derive trust boundary.
///
/// This is deliberately stricter than ordinary declaration registration.
/// Explicit source declarations may opt into `sorry` or trusted recovery, but
/// an automatic derive handler is compiler-generated authority: it must never
/// manufacture trust, leak elaborator placeholders, or return an open term.
/// The kernel still performs the definitive type check after this structural
/// gate.
pub(crate) fn admit_generated_instance(
    env: &Environment,
    class_name: &str,
    ind_name: &str,
    decl_name: &Name,
    type_: &Expr,
    value: &Expr,
) -> Result<(), DeriveError> {
    if decl_name.is_anon() {
        return Err(admission_error(
            class_name,
            ind_name,
            "handler returned an anonymous declaration name",
        ));
    }

    admit_generated_expr_shape(class_name, ind_name, "instance type", type_)?;
    admit_generated_expr_shape(class_name, ind_name, "instance value", value)?;
    let allowed_handler_axioms = registered_handler_axiom_authority(env, class_name, value);
    admit_generated_constant_closure(
        env,
        class_name,
        ind_name,
        "generated instance",
        &[type_, value],
        true,
        &allowed_handler_axioms,
    )
}

/// Return the exact axiom authority explicitly selected by a registered user
/// derive handler that occurs in this generated value.
///
/// A source declaration such as `@[derive_handler] axiom deriveMarker ...` is
/// already an explicit trust decision in the environment. Applying that exact
/// registered handler must preserve (and expose) its dependency closure rather
/// than being misclassified as a compiler-manufactured axiom. No unrelated
/// axiom is admitted: the handler must be registered for this class and occur
/// directly in the generated value, and `sorryAx`/`trusted*` remain forbidden
/// independently below.
fn registered_handler_axiom_authority(
    env: &Environment,
    class_name: &str,
    value: &Expr,
) -> HashSet<Name> {
    let mut direct = HashSet::new();
    value.collect_constants_into(&mut direct);
    let class = Name::from_string(class_name);
    let Some(handlers) = env.get_derive_handlers(&class) else {
        return HashSet::new();
    };

    let mut allowed = HashSet::new();
    for handler in handlers {
        if !direct.contains(handler) {
            continue;
        }
        if env
            .get_const(handler)
            .is_some_and(|info| info.kind == ConstantKind::Axiom)
        {
            allowed.insert(handler.clone());
        }
        if let Some(deps) = env.axiom_deps(handler) {
            allowed.extend(deps);
        }
    }
    allowed
}

fn admit_generated_expr_shape(
    class_name: &str,
    ind_name: &str,
    role: &str,
    expr: &Expr,
) -> Result<(), DeriveError> {
    let defect = if expr.has_sorry() {
        Some("contains `sorry`/`sorryAx`")
    } else if expr.has_expr_mvar_quick() {
        Some("contains an unresolved expression metavariable")
    } else if expr.has_level_mvar_quick() {
        Some("contains an unresolved universe metavariable")
    } else if expr.has_fvar_quick() {
        Some("contains a free variable")
    } else if expr.has_loose_bvars() {
        Some("contains a loose bound variable")
    } else {
        None
    };
    if let Some(defect) = defect {
        return Err(admission_error(
            class_name,
            ind_name,
            &format!("generated {role} {defect}"),
        ));
    }
    Ok(())
}

fn admit_generated_constant_closure(
    env: &Environment,
    class_name: &str,
    ind_name: &str,
    role: &str,
    expressions: &[&Expr],
    allow_prospective_constants: bool,
    allowed_handler_axioms: &HashSet<Name>,
) -> Result<(), DeriveError> {
    let mut direct_constants = HashSet::new();
    for expr in expressions {
        expr.collect_constants_into(&mut direct_constants);
    }

    // `collect_constants` is an exact traversal over every ExprKind (including
    // metadata, cubical, and set-theoretic nodes), unlike a hand-written
    // core-only matcher that could silently miss a newly added expression
    // variant. Walk the complete environment-backed constant graph ourselves:
    // `axiom_deps` reports axioms, but an elided theorem/opaque body otherwise
    // looks like an empty dependency set and could hide its authority closure.
    let prospective_constants: HashSet<Name> = if allow_prospective_constants {
        direct_constants
            .iter()
            .filter(|name| env.get_const(name).is_none())
            .cloned()
            .collect()
    } else {
        HashSet::new()
    };
    let mut worklist: Vec<Name> = direct_constants.into_iter().collect();
    let mut visited = HashSet::new();
    // Reuse one collector for every node instead of allocating separate sets
    // for each declaration type and value in a potentially large closure.
    let mut referenced_constants = HashSet::new();
    while let Some(constant) = worklist.pop() {
        if !visited.insert(constant.clone()) {
            continue;
        }

        let Some(component) = constant.last_component() else {
            return Err(admission_error(
                class_name,
                ind_name,
                &format!("generated {role} references an anonymous constant"),
            ));
        };
        if component == "sorry" || component == "sorryAx" {
            return Err(admission_error(
                class_name,
                ind_name,
                &format!("generated {role} references `{component}`"),
            ));
        }
        if component.starts_with("trusted") {
            return Err(admission_error(
                class_name,
                ind_name,
                &format!("generated {role} references trusted primitive `{constant}`"),
            ));
        }

        let Some(info) = env.get_const(&constant) else {
            // Constructors, recursors, and projections generated together with
            // the parent are unavailable during pre-admission. The strict
            // post-registration pass below resolves and traverses them. Any
            // other missing node in a transitive closure is unauditable.
            if prospective_constants.contains(&constant) {
                continue;
            }
            return Err(admission_error(
                class_name,
                ind_name,
                &format!("generated {role} reaches unavailable constant `{constant}`"),
            ));
        };
        if info.kind == ConstantKind::Axiom
            && !is_foundational_axiom(&constant)
            && !allowed_handler_axioms.contains(&constant)
        {
            return Err(admission_error(
                class_name,
                ind_name,
                &format!(
                    "generated {role} dependency closure reaches non-foundational axiom \
                     `{constant}`"
                ),
            ));
        }
        if matches!(info.kind, ConstantKind::Theorem | ConstantKind::Opaque) && info.value.is_none()
        {
            // Proof-value-elided artifacts can retain a declaration's type but
            // not the body needed to reconstruct its authority closure.  A
            // generated instance must not treat "unavailable" as "axiom-free".
            return Err(admission_error(
                class_name,
                ind_name,
                &format!(
                    "cannot audit the elided body of {kind:?} declaration `{constant}`",
                    kind = info.kind
                ),
            ));
        }
        referenced_constants.clear();
        info.type_.collect_constants_into(&mut referenced_constants);
        if let Some(value) = &info.value {
            value.collect_constants_into(&mut referenced_constants);
        }
        worklist.extend(referenced_constants.drain());
    }

    Ok(())
}

fn admission_error(class_name: &str, ind_name: &str, reason: &str) -> DeriveError {
    DeriveError::Unsupported {
        class_name: class_name.to_owned(),
        ind_name: ind_name.to_owned(),
        reason: format!("automatic deriving admission rejected the generated instance: {reason}"),
    }
}

fn admit_generated_declaration(
    env: &Environment,
    class_name: &str,
    ind_name: &str,
    decl: &Declaration,
) -> Result<Name, DeriveError> {
    let Declaration::Definition {
        name, type_, value, ..
    } = decl
    else {
        return Err(admission_error(
            class_name,
            ind_name,
            "handler returned a non-definition declaration",
        ));
    };
    admit_generated_instance(env, class_name, ind_name, name, type_, value)?;
    Ok(name.clone())
}

/// Re-audit a generated declaration after the kernel has registered it in a
/// candidate environment.
///
/// The pre-registration audit cannot resolve prospective parent constants
/// (constructors, recursors, and projections). Querying the registered
/// declaration's exact kernel dependency closure closes that gap before the
/// candidate environment is committed.
pub(crate) fn admit_registered_generated_instance(
    env: &Environment,
    class_name: &str,
    ind_name: &str,
    decl_name: &Name,
) -> Result<(), DeriveError> {
    let Some(info) = env.get_const(decl_name) else {
        return Err(admission_error(
            class_name,
            ind_name,
            &format!("registered generated declaration `{decl_name}` is not present"),
        ));
    };
    if info.kind != ConstantKind::Definition {
        return Err(admission_error(
            class_name,
            ind_name,
            &format!(
                "registered generated declaration `{decl_name}` has unexpected kind {:?}",
                info.kind
            ),
        ));
    }
    let Some(value) = &info.value else {
        return Err(admission_error(
            class_name,
            ind_name,
            &format!("registered generated declaration `{decl_name}` has no value"),
        ));
    };

    // Resolve and traverse prospective parent constants now that the complete
    // batch is installed in the candidate environment. Unknown constants,
    // transitive trust names, and elided proof bodies all fail closed here.
    admit_generated_expr_shape(
        class_name,
        ind_name,
        "registered instance type",
        &info.type_,
    )?;
    admit_generated_expr_shape(class_name, ind_name, "registered instance value", value)?;
    let allowed_handler_axioms = registered_handler_axiom_authority(env, class_name, value);
    admit_generated_constant_closure(
        env,
        class_name,
        ind_name,
        "registered generated instance",
        &[&info.type_, value],
        false,
        &allowed_handler_axioms,
    )?;

    let Some(deps) = env.axiom_deps(decl_name) else {
        return Err(admission_error(
            class_name,
            ind_name,
            &format!("registered generated declaration `{decl_name}` is not auditable"),
        ));
    };
    let unexpected_deps: HashSet<Name> = deps
        .into_iter()
        .filter(|name| !is_foundational_axiom(name) && !allowed_handler_axioms.contains(name))
        .collect();
    if unexpected_deps.is_empty() {
        return Ok(());
    }

    let mut deps: Vec<String> = unexpected_deps
        .into_iter()
        .map(|name| name.to_string())
        .collect();
    deps.sort();
    Err(admission_error(
        class_name,
        ind_name,
        &format!(
            "registered generated declaration `{decl_name}` transitively depends on \
             non-foundational axioms: {}",
            deps.join(", ")
        ),
    ))
}

/// Trait for derive handlers that generate typeclass instances.
///
/// Implementors produce one or more [`Declaration`]s that define the typeclass
/// instance for a given inductive type. The handler receives read access to the
/// environment for looking up constructors and types, and returns declarations
/// that the caller is responsible for registering.
pub trait DeriveHandler: Send + Sync {
    /// Generate instance declarations for the given inductive type.
    ///
    /// # Arguments
    ///
    /// * `ind` - The inductive type to derive an instance for.
    /// * `env` - The environment for looking up constructors, types, etc.
    ///
    /// # Returns
    ///
    /// A vector of declarations implementing the typeclass instance.
    fn derive(
        &self,
        ind: &InductiveVal,
        env: &Environment,
    ) -> Result<Vec<Declaration>, DeriveError>;

    /// Human-readable name of the typeclass this handler targets.
    fn class_name(&self) -> &str;
}

/// Registry of derive handlers indexed by typeclass name.
///
/// Handlers are registered by class name and looked up when processing
/// `@[deriving]` attributes.
pub struct DeriveRegistry {
    pub(crate) handlers: HashMap<String, Box<dyn DeriveHandler>>,
}

impl DeriveRegistry {
    /// Create a new empty registry.
    #[must_use]
    pub fn new() -> Self {
        Self {
            handlers: HashMap::new(),
        }
    }

    /// Register a derive handler for the given typeclass name.
    ///
    /// If a handler was already registered for this class, it is replaced.
    pub fn register_handler(&mut self, class_name: &str, handler: Box<dyn DeriveHandler>) {
        self.handlers.insert(class_name.to_owned(), handler);
    }

    /// Check whether a handler is registered for the given class.
    #[must_use]
    pub fn has_handler(&self, class_name: &str) -> bool {
        self.handlers.contains_key(class_name)
    }

    /// Run the derive handler for `class_name` on the given inductive type,
    /// producing declarations and adding them to the environment.
    ///
    /// # Errors
    ///
    /// Returns [`DeriveError::NoHandler`] if no handler is registered for the
    /// class, or propagates errors from the handler or environment registration.
    pub fn run_derive(
        &self,
        class_name: &str,
        ind: &InductiveVal,
        env: &mut Environment,
    ) -> Result<(), DeriveError> {
        let handler = self
            .handlers
            .get(class_name)
            .ok_or_else(|| DeriveError::NoHandler(class_name.to_owned()))?;

        let decls = handler.derive(ind, env)?;
        let ind_name = ind.name.to_string();

        // Validate the complete batch before any candidate mutation. A later
        // forbidden declaration must not leave earlier generated declarations
        // partially registered.
        let admitted_names: Vec<Name> = decls
            .iter()
            .map(|decl| admit_generated_declaration(env, class_name, &ind_name, decl))
            .collect::<Result<_, _>>()?;
        if decls.is_empty() {
            return Ok(());
        }

        // `Environment::add_decl` is atomic per declaration, not across a
        // handler's batch. Register into a clone so a late duplicate or kernel
        // error cannot leave a prefix of generated declarations installed.
        let mut candidate = env.clone();
        for (decl, name) in decls.into_iter().zip(&admitted_names) {
            // Retain the exact kernel Name collected during admission instead
            // of round-tripping through display text (numeric name components
            // are not required to parse back identically).
            let decl_name = name.to_string();
            candidate
                .add_decl(decl)
                .map_err(|e| DeriveError::RegistrationFailed {
                    name: decl_name,
                    detail: e.to_string(),
                })?;
        }
        for name in &admitted_names {
            admit_registered_generated_instance(&candidate, class_name, &ind_name, name)?;
        }
        *env = candidate;

        Ok(())
    }

    /// List all registered handler class names.
    #[must_use]
    pub fn registered_classes(&self) -> Vec<&str> {
        self.handlers.keys().map(String::as_str).collect()
    }
}

impl Default for DeriveRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl std::fmt::Debug for DeriveRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DeriveRegistry")
            .field("handlers", &self.handlers.keys().collect::<Vec<_>>())
            .finish()
    }
}

/// Build a fully-qualified instance name: `inst{ClassName}{TypeName}`.
///
/// Follows Lean 4's naming convention for auto-derived instances.
pub(crate) fn instance_name(class_name: &str, type_name: &Name) -> Name {
    Name::from_string(&format!("inst{class_name}{}", type_name))
}
