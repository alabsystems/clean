// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! User-defined `deriving` handlers (Phase 3 extensibility surface).
//!
//! Mirrors the user-defined attribute and tactic facilities: a Clean-native
//! registry that lets a project register its own `deriving MyClass` behaviour,
//! dispatched by class name. No dependency on Lean `.olean` metaprograms — the
//! builtin deriving classes (`BEq`, `DecidableEq`, …) stay in [`crate::infer`]'s
//! native dispatch; this registry is the extension point for *new* classes.

use std::collections::HashMap;
use std::sync::Arc;

use clean_kernel::{Declaration, Environment, Name};

use crate::error::ElabError;

/// A user-supplied handler for `deriving <Class>`. Invoked with the target type's
/// declaration name and the current kernel [`Environment`]; returns the instance
/// declaration(s) to register, or an [`ElabError`] to fail elaboration loudly.
pub type UserDerivingHandler =
    Arc<dyn Fn(&Name, &Environment) -> Result<Vec<Declaration>, ElabError> + Send + Sync>;

/// Registry of user-defined deriving handlers, keyed by class name (e.g. `"BEq"`).
/// Independent of the builtin deriving dispatch in [`crate::infer`]; this is the
/// Phase 3 extension point for `deriving MyClass`.
#[derive(Clone, Default)]
pub struct UserDerivingRegistry {
    handlers: HashMap<String, UserDerivingHandler>,
}

impl std::fmt::Debug for UserDerivingRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("UserDerivingRegistry")
            .field("classes", &self.handlers.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl UserDerivingRegistry {
    /// Create an empty registry.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a handler for `deriving <class>`. A later registration for the
    /// same class replaces the earlier one (last-wins, as in Lean).
    pub fn register(&mut self, class: impl Into<String>, handler: UserDerivingHandler) {
        self.handlers.insert(class.into(), handler);
    }

    /// Whether a handler is registered for `deriving <class>`.
    #[must_use]
    pub fn is_registered(&self, class: &str) -> bool {
        self.handlers.contains_key(class)
    }

    /// Number of registered deriving classes.
    #[must_use]
    pub fn registered_count(&self) -> usize {
        self.handlers.len()
    }

    /// Names of all registered deriving classes.
    pub fn class_names(&self) -> impl Iterator<Item = &str> {
        self.handlers.keys().map(String::as_str)
    }

    /// Generate the instance declaration(s) for `deriving <class>` on `target`.
    /// Fails with [`ElabError::Unsupported`] if no handler is registered for
    /// `class`; otherwise propagates the handler's own result.
    pub fn derive(
        &self,
        class: &str,
        target: &Name,
        env: &Environment,
    ) -> Result<Vec<Declaration>, ElabError> {
        let handler = self
            .handlers
            .get(class)
            .ok_or_else(|| ElabError::Unsupported {
                feature: format!("no user deriving handler registered for class '{class}'"),
            })?;
        handler(target, env)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::{Expr, Level};

    fn env_with_type(type_name: &str) -> Environment {
        let mut env = Environment::new();
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(type_name),
            level_params: vec![],
            type_: Expr::sort(Level::zero()),
        })
        .expect("add type decl");
        env
    }

    #[test]
    fn test_user_deriving_registry_dispatches_and_returns_instances() {
        let env = env_with_type("Foo");
        let mut reg = UserDerivingRegistry::new();
        reg.register(
            "MyClass",
            Arc::new(|target: &Name, _env: &Environment| {
                // A handler produces the instance declaration(s) for the target.
                Ok(vec![Declaration::Axiom {
                    name: Name::from_string(&format!("instMyClass_{target}")),
                    level_params: vec![],
                    type_: Expr::sort(Level::zero()),
                }])
            }),
        );

        assert!(reg.is_registered("MyClass"));
        assert_eq!(reg.registered_count(), 1);
        assert_eq!(reg.class_names().collect::<Vec<_>>(), vec!["MyClass"]);

        let decls = reg
            .derive("MyClass", &Name::from_string("Foo"), &env)
            .expect("handler should produce instances for a known class");
        assert_eq!(decls.len(), 1, "one instance generated");
    }

    #[test]
    fn test_user_deriving_registry_unknown_class_is_unsupported_error() {
        let env = env_with_type("Foo");
        let reg = UserDerivingRegistry::new();
        let err = reg
            .derive("NotRegistered", &Name::from_string("Foo"), &env)
            .expect_err("an unregistered deriving class must fail loudly");
        assert!(
            matches!(err, ElabError::Unsupported { .. }),
            "expected Unsupported, got {err:?}"
        );
    }

    #[test]
    fn test_user_deriving_registry_handler_error_propagates() {
        let env = env_with_type("Foo");
        let mut reg = UserDerivingRegistry::new();
        reg.register(
            "Strict",
            Arc::new(|target: &Name, _env: &Environment| {
                if target == &Name::from_string("Unsupported") {
                    Err(ElabError::Unsupported {
                        feature: "cannot derive Strict for this type".into(),
                    })
                } else {
                    Ok(Vec::new())
                }
            }),
        );
        assert!(
            reg.derive("Strict", &Name::from_string("Unsupported"), &env)
                .is_err(),
            "handler should reject an unsupported target"
        );
        reg.derive("Strict", &Name::from_string("Foo"), &env)
            .expect("handler should accept a supported target");
    }

    #[test]
    fn test_user_deriving_registry_last_registration_wins() {
        let env = env_with_type("Foo");
        let mut reg = UserDerivingRegistry::new();
        reg.register(
            "C",
            Arc::new(|_t: &Name, _e: &Environment| {
                Err(ElabError::Unsupported {
                    feature: "first handler (should be replaced)".into(),
                })
            }),
        );
        reg.register("C", Arc::new(|_t: &Name, _e: &Environment| Ok(Vec::new())));
        assert_eq!(
            reg.registered_count(),
            1,
            "re-registering the same class replaces, not appends"
        );
        reg.derive("C", &Name::from_string("Foo"), &env)
            .expect("the second (last) registered handler should win");
    }
}
