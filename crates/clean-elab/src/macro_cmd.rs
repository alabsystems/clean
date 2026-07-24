// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Macro command framework for Lean 5.
//!
//! Provides a registry for user-defined macros that transform surface syntax.
//! Macros are matched by name and their arguments are substituted into an
//! expansion template to produce a new `SurfaceExpr`.
//!
//! # Architecture
//!
//! The macro command framework operates at the surface syntax level, before
//! elaboration. Each macro has a name, a pattern describing its expected
//! arguments, an expansion template, and a scoping category (command, term,
//! or tactic).
//!
//! This complements the `macro_integration` module which handles the
//! lower-level `Syntax`-based macro system from `clean-macro`. This module
//! provides a higher-level, template-based system for simple macros like
//! `#check`, `#eval`, and `#print`.
//!
//! # Example
//!
//! ```
//! use clean_elab::macro_cmd::{MacroDef, MacroPatternPart, MacroRegistry, MacroScoping};
//! use clean_parser::{Span, SurfaceExpr};
//!
//! let mut registry = MacroRegistry::new();
//! registry.register(MacroDef {
//!     name: "double".to_owned(),
//!     pattern: vec![MacroPatternPart::Expr],
//!     expansion_template: SurfaceExpr::App(
//!         Span::new(0, 0),
//!         Box::new(SurfaceExpr::Ident(Span::new(0, 0), "Nat.add".to_owned())),
//!         vec![],  // Arguments substituted at expansion time
//!     ),
//!     scoping: MacroScoping::Term,
//! });
//! assert!(registry.lookup("double").is_some());
//! ```

use std::collections::HashMap;

use clean_parser::{Span, SurfaceArg, SurfaceExpr};

/// Error type for macro expansion failures.
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum MacroError {
    /// Referenced a macro that is not registered.
    #[error("unknown macro: {0}")]
    UnknownMacro(String),
    /// Wrong number of arguments passed to the macro.
    #[error("macro '{name}' expects {expected} argument(s), got {actual}")]
    ArityMismatch {
        name: String,
        expected: usize,
        actual: usize,
    },
    /// A required expression argument was missing.
    #[error("macro '{name}': missing required expression argument at position {position}")]
    MissingArgument { name: String, position: usize },
    /// Expansion template substitution failed.
    #[error("macro '{name}' expansion failed: {detail}")]
    ExpansionFailed { name: String, detail: String },
}

/// A single part of a macro's expected argument pattern.
///
/// Describes what kind of syntactic element the macro expects at each
/// argument position.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum MacroPatternPart {
    /// A literal keyword that must appear: `"check"`, `"eval"`, etc.
    Keyword(String),
    /// An identifier argument.
    Ident,
    /// An expression argument (the most common).
    Expr,
    /// An optional expression argument.
    OptionalExpr,
    /// A separated-by list of expressions: `expr "," expr "," ...`
    SepByExpr(String),
}

/// The scoping category for a macro, controlling where it can appear.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum MacroScoping {
    /// A command-level macro (e.g., `#check`, `#eval`, `#print`).
    Command,
    /// A term-level macro (expands inside expressions).
    Term,
    /// A tactic-level macro (expands inside tactic blocks).
    Tactic,
}

/// A macro definition: name, pattern, expansion template, and scoping.
///
/// The `expansion_template` is a `SurfaceExpr` that serves as the skeleton
/// of the expansion. During expansion, `Expr` pattern parts are substituted
/// into the template at placeholder positions.
#[derive(Debug, Clone)]
pub struct MacroDef {
    /// The name used to invoke the macro (e.g., `"check"` for `#check`).
    pub name: String,
    /// The expected argument pattern.
    pub pattern: Vec<MacroPatternPart>,
    /// The expansion template. `Hole` nodes in the template are replaced
    /// with the corresponding arguments during expansion.
    pub expansion_template: SurfaceExpr,
    /// Where this macro can appear.
    pub scoping: MacroScoping,
}

impl MacroDef {
    /// Count the number of required expression arguments in the pattern.
    #[must_use]
    pub fn required_arity(&self) -> usize {
        self.pattern
            .iter()
            .filter(|p| matches!(p, MacroPatternPart::Expr | MacroPatternPart::Ident))
            .count()
    }
}

/// Registry of macro definitions, keyed by name.
///
/// Constructed via [`MacroRegistry::new`] which pre-registers built-in
/// command macros (`#check`, `#eval`, `#print`). Users can register
/// additional macros via [`MacroRegistry::register`].
pub struct MacroRegistry {
    entries: HashMap<String, MacroDef>,
}

impl std::fmt::Debug for MacroRegistry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MacroRegistry")
            .field("count", &self.entries.len())
            .field("names", &self.entries.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl Default for MacroRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl MacroRegistry {
    /// Create a new registry with built-in command macros pre-registered.
    ///
    /// Pre-registers `#check`, `#eval`, and `#print` as command-scoped macros.
    #[must_use]
    pub fn new() -> Self {
        let mut registry = Self {
            entries: HashMap::new(),
        };
        register_builtin_macros(&mut registry);
        registry
    }

    /// Create a new empty registry without built-in macros.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            entries: HashMap::new(),
        }
    }

    /// Register a macro definition.
    ///
    /// If a macro with the same name already exists, it is replaced.
    pub fn register(&mut self, def: MacroDef) {
        self.entries.insert(def.name.clone(), def);
    }

    /// Look up a macro definition by name.
    #[must_use]
    pub fn lookup(&self, name: &str) -> Option<&MacroDef> {
        self.entries.get(name)
    }

    /// Check whether a macro is registered.
    #[must_use]
    pub fn is_registered(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// Number of registered macros.
    #[must_use]
    pub fn count(&self) -> usize {
        self.entries.len()
    }

    /// Iterate over all registered macro names.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.entries.keys().map(|s| s.as_str())
    }

    /// Iterate over all registered macro definitions.
    pub fn all_macros(&self) -> impl Iterator<Item = &MacroDef> {
        self.entries.values()
    }
}

/// Expand a macro by name with the given arguments.
///
/// Looks up the macro in the registry, validates argument count, and
/// substitutes arguments into the expansion template. For simple macros
/// (like `#check expr`), the expansion wraps the argument in the template.
///
/// # Errors
///
/// Returns [`MacroError::UnknownMacro`] if the macro is not registered.
/// Returns [`MacroError::ArityMismatch`] if the wrong number of arguments
/// is provided.
pub fn expand_macro(
    registry: &MacroRegistry,
    name: &str,
    args: &[SurfaceExpr],
) -> Result<SurfaceExpr, MacroError> {
    let def = registry
        .lookup(name)
        .ok_or_else(|| MacroError::UnknownMacro(name.to_owned()))?;

    let required = def.required_arity();
    if args.len() < required {
        return Err(MacroError::ArityMismatch {
            name: name.to_owned(),
            expected: required,
            actual: args.len(),
        });
    }

    substitute_template(&def.expansion_template, &def.name, args)
}

/// Substitute arguments into a template expression.
///
/// Replaces `Hole` nodes in the template with the corresponding arguments
/// (by position). If the template is an `App` node, arguments are appended
/// as application arguments. For other templates, the first argument is
/// substituted for the first hole encountered in a depth-first traversal.
fn substitute_template(
    template: &SurfaceExpr,
    macro_name: &str,
    args: &[SurfaceExpr],
) -> Result<SurfaceExpr, MacroError> {
    match template {
        // Application node: append args as positional arguments
        SurfaceExpr::App(span, func, existing_args) => {
            let mut new_args: Vec<SurfaceArg> = existing_args.clone();
            for arg in args {
                new_args.push(SurfaceArg::positional(arg.clone()));
            }
            Ok(SurfaceExpr::App(*span, func.clone(), new_args))
        }
        // Identifier: wrap in application with arguments
        SurfaceExpr::Ident(span, _) => {
            if args.is_empty() {
                Ok(template.clone())
            } else {
                let surface_args: Vec<SurfaceArg> = args
                    .iter()
                    .map(|a| SurfaceArg::positional(a.clone()))
                    .collect();
                Ok(SurfaceExpr::App(
                    *span,
                    Box::new(template.clone()),
                    surface_args,
                ))
            }
        }
        // Hole: replace with first argument
        SurfaceExpr::Hole(_span) => {
            if args.is_empty() {
                Err(MacroError::MissingArgument {
                    name: macro_name.to_owned(),
                    position: 0,
                })
            } else {
                Ok(args[0].clone())
            }
        }
        // For other templates, clone as-is (no substitution points)
        other => {
            if args.is_empty() {
                Ok(other.clone())
            } else {
                // Wrap in application
                let surface_args: Vec<SurfaceArg> = args
                    .iter()
                    .map(|a| SurfaceArg::positional(a.clone()))
                    .collect();
                Ok(SurfaceExpr::App(
                    Span::new(0, 0),
                    Box::new(other.clone()),
                    surface_args,
                ))
            }
        }
    }
}

/// Register built-in command macros: `#check`, `#eval`, `#print`.
///
/// These correspond to the interactive commands already partially handled
/// in `commands.rs`. The macro framework wraps them so they can be
/// expanded uniformly through the macro pipeline.
fn register_builtin_macros(registry: &mut MacroRegistry) {
    // #check <expr> -- type-check and display the type
    registry.register(MacroDef {
        name: "check".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: SurfaceExpr::Ident(Span::new(0, 0), "#check".to_owned()),
        scoping: MacroScoping::Command,
    });

    // #eval <expr> -- evaluate and display the result
    registry.register(MacroDef {
        name: "eval".to_owned(),
        pattern: vec![MacroPatternPart::Expr],
        expansion_template: SurfaceExpr::Ident(Span::new(0, 0), "#eval".to_owned()),
        scoping: MacroScoping::Command,
    });

    // #print <ident> -- print a declaration's definition
    registry.register(MacroDef {
        name: "print".to_owned(),
        pattern: vec![MacroPatternPart::Ident],
        expansion_template: SurfaceExpr::Ident(Span::new(0, 0), "#print".to_owned()),
        scoping: MacroScoping::Command,
    });
}

#[cfg(test)]
#[path = "macro_cmd_tests.rs"]
mod tests;
