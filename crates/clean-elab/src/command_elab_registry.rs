// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Attribute command elaboration registry for Lean 5.
//!
//! Provides a registry for attribute command handlers, enabling processing of
//! built-in attributes like `@[reducible]`, `@[simp]`, `@[inline]`,
//! `@[instance]`, and `@[extern]`. Each attribute kind can have multiple
//! handlers sorted by priority (higher priority first).
//!
//! # Architecture
//!
//! The registry stores [`CommandElabEntry`] values in a `HashMap<String, Vec<_>>`
//! keyed by command name. When attribute processing encounters a command with
//! registered handlers, it tries each handler in priority order until one
//! succeeds.
//!
//! This mirrors Lean 4's `@[command_elab]` attribute from
//! `Lean.Elab.Command.Basic` where multiple elaborators can be registered for
//! the same command kind and are tried in priority order.
//!
//! # Example
//!
//! ```
//! use clean_elab::command_elab_registry::CommandElabRegistry;
//!
//! let registry = CommandElabRegistry::new();
//! assert!(registry.is_registered("reducible"));
//! assert!(registry.is_registered("simp"));
//! assert!(registry.is_registered("inline"));
//! assert!(registry.is_registered("instance"));
//! assert!(registry.is_registered("extern"));
//! ```

use std::collections::HashMap;
use std::sync::Arc;

use crate::derive_handlers::register_user_derive_handler;
use crate::ElabError;
use clean_kernel::env::{Reducibility, SimpPriority, TrustedEnvExt};
use clean_kernel::{Environment, Name};

/// Context for attribute command elaboration.
///
/// Carries the declaration name and a mutable reference to the environment
/// so handlers can register attributes in the kernel.
pub struct CommandElabCtx<'a> {
    /// The declaration name the attribute is being applied to.
    pub decl_name: Name,
    /// Mutable environment for attribute registration.
    pub env: &'a mut Environment,
}

/// Callback type for attribute command handlers.
///
/// Parameters:
/// - `ctx`: the command elaboration context with environment access
/// - `args`: optional arguments passed to the attribute (e.g., priority)
///
/// Returns `Ok(())` on success, or an `ElabError` on failure. When a handler
/// returns an error, the registry tries the next handler in priority order.
pub type CommandElabFn =
    dyn Fn(&mut CommandElabCtx<'_>, &[String]) -> Result<(), ElabError> + Send + Sync;

/// A registered command elaborator entry.
///
/// Each entry associates a command name with a handler function and a priority.
/// Multiple entries can share the same command name; they are tried in
/// descending priority order (higher numeric value = tried first).
pub struct CommandElabEntry {
    /// The command name this elaborator handles (e.g., `"reducible"`).
    pub command_name: String,
    /// The elaboration handler function.
    pub handler: Arc<CommandElabFn>,
    /// Priority for dispatch ordering. Higher values are tried first.
    /// Default priority for builtin elaborators is 1000.
    pub priority: u32,
}

impl Clone for CommandElabEntry {
    fn clone(&self) -> Self {
        Self {
            command_name: self.command_name.clone(),
            handler: Arc::clone(&self.handler),
            priority: self.priority,
        }
    }
}

impl std::fmt::Debug for CommandElabEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CommandElabEntry")
            .field("command_name", &self.command_name)
            .field("priority", &self.priority)
            .field("handler", &"<fn>")
            .finish()
    }
}

/// Default priority for builtin command elaborators.
pub(crate) const DEFAULT_PRIORITY: u32 = 1000;

/// Registry of attribute command elaborators, keyed by command name.
///
/// Constructed via [`CommandElabRegistry::new`] which pre-registers handlers for
/// common attribute commands (reducible, simp, inline, instance, extern). Users
/// can register additional handlers via [`CommandElabRegistry::register`].
///
/// When multiple handlers are registered for the same command, they are stored
/// in descending priority order and tried sequentially during elaboration.
pub struct CommandElabRegistry {
    entries: HashMap<String, Vec<CommandElabEntry>>,
}

impl std::fmt::Debug for CommandElabRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CommandElabRegistry")
            .field("kind_count", &self.entries.len())
            .field("kinds", &self.entries.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl CommandElabRegistry {
    /// Create a new registry with builtin attribute handlers pre-registered.
    ///
    /// Pre-registers handlers for common attribute commands at
    /// [`DEFAULT_PRIORITY`]: `reducible`, `simp`, `inline`, `instance`,
    /// `extern`, `irreducible`, `semireducible`.
    #[must_use]
    pub fn new() -> Self {
        let mut registry = Self {
            entries: HashMap::new(),
        };
        register_builtin_command_elaborators(&mut registry);
        registry
    }

    /// Register a command elaborator for a given command name.
    ///
    /// Inserts the entry into the handler list for `name`, maintaining
    /// descending priority order. Multiple handlers per command are supported.
    pub fn register(&mut self, name: &str, entry: CommandElabEntry) {
        let handlers = self.entries.entry(name.to_owned()).or_default();
        let pos = handlers
            .iter()
            .position(|e| e.priority < entry.priority)
            .unwrap_or(handlers.len());
        handlers.insert(pos, entry);
    }

    /// Try to elaborate a command using registered handlers for `name`.
    ///
    /// Tries each handler in descending priority order. Returns the result
    /// from the first handler that succeeds. If all handlers fail, returns
    /// the error from the last handler tried. If no handlers are registered,
    /// returns `None`.
    #[must_use = "elaboration result should be checked"]
    pub fn elaborate(
        &self,
        name: &str,
        ctx: &mut CommandElabCtx<'_>,
        args: &[String],
    ) -> Option<Result<(), ElabError>> {
        let handlers = self.entries.get(name)?;
        if handlers.is_empty() {
            return None;
        }

        let mut last_err = None;
        for entry in handlers {
            match (entry.handler)(ctx, args) {
                Ok(()) => return Some(Ok(())),
                Err(e) => last_err = Some(e),
            }
        }

        last_err.map(Err)
    }

    /// Check whether any handlers are registered for a command name.
    #[must_use]
    pub fn is_registered(&self, name: &str) -> bool {
        self.entries.get(name).is_some_and(|v| !v.is_empty())
    }

    /// Look up all handlers for a command name, in priority order.
    #[must_use]
    pub fn get_handlers(&self, name: &str) -> Option<&[CommandElabEntry]> {
        self.entries.get(name).map(|v| v.as_slice())
    }

    /// Number of distinct command names with registered handlers.
    #[must_use]
    pub fn kind_count(&self) -> usize {
        self.entries.len()
    }

    /// Total number of registered handler entries across all command names.
    #[must_use]
    pub fn handler_count(&self) -> usize {
        self.entries.values().map(|v| v.len()).sum()
    }

    /// Iterate over all registered command names.
    pub fn kinds(&self) -> impl Iterator<Item = &str> {
        self.entries.keys().map(|s| s.as_str())
    }
}

impl Default for CommandElabRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Builtin attribute command names pre-registered at construction.
///
/// These correspond to the core Lean 4 attributes that affect compilation
/// and reduction behavior. Each has a handler that modifies the kernel
/// environment's attribute registries.
pub(crate) const BUILTIN_COMMAND_KINDS: &[&str] = &[
    "reducible",
    "semireducible",
    "irreducible",
    "simp",
    "inline",
    "instance",
    "extern",
    "derive_handler",
];

/// Register all builtin attribute command handlers.
///
/// Delegates to per-group registration functions to stay within function
/// size limits. Each handler interacts with the kernel environment to
/// record the attribute effect.
fn register_builtin_command_elaborators(registry: &mut CommandElabRegistry) {
    register_reducibility_handlers(registry);
    register_simp_handler(registry);
    register_inline_handler(registry);
    register_instance_handler(registry);
    register_extern_handler(registry);
    register_derive_handler_handler(registry);
}

/// Register @[reducible], @[semireducible], @[irreducible] handlers.
fn register_reducibility_handlers(registry: &mut CommandElabRegistry) {
    registry.register(
        "reducible",
        CommandElabEntry {
            command_name: "reducible".to_owned(),
            handler: Arc::new(|ctx, _args| {
                ctx.env
                    .set_reducibility(&ctx.decl_name, Reducibility::Reducible);
                Ok(())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );

    registry.register(
        "semireducible",
        CommandElabEntry {
            command_name: "semireducible".to_owned(),
            handler: Arc::new(|ctx, _args| {
                ctx.env
                    .set_reducibility(&ctx.decl_name, Reducibility::SEMIREDUCIBLE);
                Ok(())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );

    registry.register(
        "irreducible",
        CommandElabEntry {
            command_name: "irreducible".to_owned(),
            handler: Arc::new(|ctx, _args| {
                ctx.env
                    .set_reducibility(&ctx.decl_name, Reducibility::Irreducible);
                Ok(())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );
}

/// Register @[simp] handler with optional priority argument.
fn register_simp_handler(registry: &mut CommandElabRegistry) {
    registry.register(
        "simp",
        CommandElabEntry {
            command_name: "simp".to_owned(),
            handler: Arc::new(|ctx, args| {
                let priority = if let Some(p_str) = args.first() {
                    let p = p_str.parse::<u32>().map_err(|_| {
                        ElabError::NotImplemented(format!(
                            "@[simp] priority must be a u32, got '{p_str}'"
                        ))
                    })?;
                    SimpPriority::Custom(p)
                } else {
                    SimpPriority::Default
                };
                ctx.env.register_simp_lemma(ctx.decl_name.clone(), priority);
                Ok(())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );
}

/// Register @[inline] handler.
fn register_inline_handler(registry: &mut CommandElabRegistry) {
    registry.register(
        "inline",
        CommandElabEntry {
            command_name: "inline".to_owned(),
            handler: Arc::new(|ctx, _args| {
                ctx.env.register_inline(ctx.decl_name.clone());
                Ok(())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );
}

/// Register @[instance] handler with optional priority argument.
fn register_instance_handler(registry: &mut CommandElabRegistry) {
    registry.register(
        "instance",
        CommandElabEntry {
            command_name: "instance".to_owned(),
            handler: Arc::new(|ctx, args| {
                let priority = if let Some(p_str) = args.first() {
                    p_str.parse::<u32>().map_err(|_| {
                        ElabError::NotImplemented(format!(
                            "@[instance] priority must be a u32, got '{p_str}'"
                        ))
                    })?
                } else {
                    clean_kernel::DEFAULT_INSTANCE_PRIORITY
                };
                let info = clean_kernel::KernelInstanceInfo {
                    name: ctx.decl_name.clone(),
                    // Placeholder: real class extraction requires type analysis
                    class_name: ctx.decl_name.clone(),
                    priority,
                    type_: None,
                    value: None,
                };
                ctx.env.register_instance(info);
                Ok(())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );
}

/// Register @[extern "cname"] handler.
fn register_extern_handler(registry: &mut CommandElabRegistry) {
    registry.register(
        "extern",
        CommandElabEntry {
            command_name: "extern".to_owned(),
            handler: Arc::new(|ctx, args| {
                let extern_name = args
                    .first()
                    .cloned()
                    .unwrap_or_else(|| ctx.decl_name.to_string());
                ctx.env.register_extern(ctx.decl_name.clone(), extern_name);
                Ok(())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );
}

/// Register @[derive_handler] handler.
fn register_derive_handler_handler(registry: &mut CommandElabRegistry) {
    registry.register(
        "derive_handler",
        CommandElabEntry {
            command_name: "derive_handler".to_owned(),
            handler: Arc::new(|ctx, _args| {
                register_user_derive_handler(ctx.env, &ctx.decl_name).map(|_| ())
            }),
            priority: DEFAULT_PRIORITY,
        },
    );
}

#[cfg(test)]
#[path = "command_elab_registry_tests.rs"]
mod tests;
