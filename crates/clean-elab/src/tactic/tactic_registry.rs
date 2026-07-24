// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! User-defined tactic registration for `@[tactic]`-style extensibility.
//!
//! Provides [`UserTacticRegistry`] for registering custom tactic handlers by
//! name at elaboration time, replacing the need to hardcode every tactic in
//! `builtins.rs`. This enables Lean 4-compatible `@[tactic myTacticKind]`
//! registration.
//!
//! # Architecture
//!
//! This module is the user-facing registration layer. It wraps the internal
//! [`super::registry::TacticRegistry`] (which dispatches built-in tactics via
//! pre-elaborated `Expr` arguments) and adds a separate table for user-defined
//! tactics that receive raw `SurfaceTactic` arguments — matching the Lean 4
//! pattern where user tactics operate on syntax rather than elaborated terms.
//!
//! # Usage
//!
//! ```text
//! let mut reg = UserTacticRegistry::new();
//! reg.register("my_tactic", |args, ps| { /* ... */ Ok(()) }, "My custom tactic");
//! reg.dispatch("my_tactic", &[], &mut proof_state)?;
//! ```

use std::collections::HashMap;
use std::sync::Arc;

use clean_parser::SurfaceTactic;

use super::{ProofState, TacticError, TacticResult};

/// Handler function for user-defined tactics.
///
/// Receives the raw surface-level tactic arguments (pre-elaboration) and a
/// mutable proof state. This matches the Lean 4 `@[tactic]` model where
/// user-registered tactics operate on syntax objects.
pub type UserTacticHandler =
    Arc<dyn Fn(&[SurfaceTactic], &mut ProofState) -> TacticResult + Send + Sync>;

/// A registered user-defined tactic entry.
///
/// Stores the tactic name, handler function, and a human-readable description
/// (for documentation, `#help tactic`, and error messages).
#[derive(Clone)]
pub struct UserTacticEntry {
    /// Tactic name as written in Lean syntax (e.g., `"my_custom_tactic"`).
    pub(crate) name: String,
    /// Handler invoked when this tactic is dispatched.
    pub(crate) handler: UserTacticHandler,
    /// Human-readable description for `#help tactic` and diagnostics.
    pub(crate) description: String,
}

impl UserTacticEntry {
    /// The registered tactic name.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Human-readable description of this tactic.
    #[must_use]
    pub fn description(&self) -> &str {
        &self.description
    }
}

/// Registry for user-defined tactic handlers.
///
/// Provides `@[tactic]`-style extensibility: users register custom tactic
/// handlers by name, and [`dispatch`](Self::dispatch) looks up and invokes the
/// matching handler at elaboration time.
///
/// Built-in tactics (intro, apply, simp, etc.) are pre-registered during
/// construction via [`with_builtins`](Self::with_builtins).
#[derive(Clone, Default)]
pub struct UserTacticRegistry {
    entries: HashMap<String, UserTacticEntry>,
}

impl UserTacticRegistry {
    /// Create an empty registry with no tactics registered.
    ///
    /// ENSURES: `is_empty()` returns `true`.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a registry pre-populated with all built-in tactic stubs.
    ///
    /// Each built-in tactic is registered as a stub that delegates to the
    /// internal `TacticRegistry` dispatch at the elaboration layer. This
    /// provides a unified lookup surface for both built-in and user-defined
    /// tactics.
    ///
    /// ENSURES: All core tactics (intro, intros, exact, apply, rfl, assumption,
    ///          constructor, cases, induction, simp, sorry) are registered.
    #[must_use]
    pub fn with_builtins() -> Self {
        let mut reg = Self::new();
        register_builtin_stubs(&mut reg);
        reg
    }

    /// Register a user-defined tactic.
    ///
    /// Overwrites any previous registration for the same name.
    ///
    /// REQUIRES: `name` is non-empty.
    /// ENSURES: `get(name)` returns the newly registered entry.
    /// ENSURES: `dispatch(name, args, ps)` invokes `handler(args, ps)`.
    pub fn register(
        &mut self,
        name: &str,
        handler: impl Fn(&[SurfaceTactic], &mut ProofState) -> TacticResult + Send + Sync + 'static,
        description: &str,
    ) {
        self.entries.insert(
            name.to_string(),
            UserTacticEntry {
                name: name.to_string(),
                handler: Arc::new(handler),
                description: description.to_string(),
            },
        );
    }

    /// Look up a tactic entry by name.
    ///
    /// ENSURES: Returns `Some` iff a tactic is registered under `name`.
    #[must_use]
    pub fn get(&self, name: &str) -> Option<&UserTacticEntry> {
        self.entries.get(name)
    }

    /// Dispatch a tactic by name: look up the handler and invoke it.
    ///
    /// Returns `TacticError::UnknownTactic` if no tactic is registered under
    /// the given name.
    ///
    /// REQUIRES: `state` is a valid proof state with at least one goal (for
    ///           most tactics; some like `done` check explicitly).
    /// ENSURES: On `Ok`, the handler's effects are applied to `state`.
    /// ENSURES: On `Err(UnknownTactic)`, `state` is unchanged.
    pub fn dispatch(
        &self,
        name: &str,
        args: &[SurfaceTactic],
        state: &mut ProofState,
    ) -> TacticResult {
        let entry = self
            .entries
            .get(name)
            .ok_or_else(|| TacticError::UnknownTactic(name.to_string()))?;
        (entry.handler)(args, state)
    }

    /// Check if a tactic name is registered.
    ///
    /// ENSURES: Returns `true` exactly when `get(name)` would return `Some`.
    #[must_use]
    pub fn is_registered(&self, name: &str) -> bool {
        self.entries.contains_key(name)
    }

    /// Iterator over all registered tactic names.
    ///
    /// ENSURES: Yields each registered name exactly once.
    pub fn names(&self) -> impl Iterator<Item = &str> {
        self.entries.keys().map(|s| s.as_str())
    }

    /// Number of registered tactics.
    #[must_use]
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Whether the registry is empty.
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }
}

/// Register stub entries for all core built-in tactics.
///
/// Each stub delegates to the corresponding tactic function from the tactic
/// module. The stubs ignore `SurfaceTactic` args (built-in tactics receive
/// their arguments via the internal elaboration pipeline, not via the
/// user-facing surface args).
fn register_builtin_stubs(reg: &mut UserTacticRegistry) {
    register_nullary_builtins(reg);
    register_arg_builtins(reg);
}

/// Register nullary built-in tactic stubs.
fn register_nullary_builtins(reg: &mut UserTacticRegistry) {
    let nullary_builtins: &[(&str, fn(&mut ProofState) -> TacticResult, &str)] = &[
        (
            "assumption",
            super::assumption,
            "Close goal using a hypothesis from the local context",
        ),
        (
            "constructor",
            super::constructor,
            "Apply a constructor of an inductive type",
        ),
        ("rfl", super::rfl, "Close goal by reflexivity (a = a)"),
        (
            "sorry",
            super::sorry,
            "Admit the current goal without proof (WARNING: unsound)",
        ),
        (
            "intro",
            |ps| super::intro(ps, "h"),
            "Introduce a binder from the goal into the context",
        ),
        (
            "intros",
            |ps| {
                let mut count = 0;
                while super::intro(ps, &format!("h_{count}")).is_ok() {
                    count += 1;
                }
                Ok(())
            },
            "Introduce all binders from the goal",
        ),
        (
            "left",
            super::left_,
            "Prove a disjunction by proving the left alternative",
        ),
        (
            "right",
            super::right_,
            "Prove a disjunction by proving the right alternative",
        ),
        (
            "split",
            super::split_,
            "Split a conjunction goal into two subgoals",
        ),
        ("exfalso", super::exfalso, "Change the goal to False"),
        (
            "contradiction",
            super::contradiction,
            "Close the goal by finding contradictory hypotheses",
        ),
        (
            "trivial",
            super::trivial,
            "Close the goal using simple logic",
        ),
        ("symm", super::symm, "Swap sides of an equality or relation"),
        (
            "omega",
            super::omega,
            "Solve linear arithmetic over naturals and integers",
        ),
        (
            "cert_mathverse",
            super::cert_mathverse,
            "Normalize certificate arithmetic goals, then call mathverse with diagnostics",
        ),
        (
            "cert_simp",
            super::cert_simp,
            "Simplify certificate/list arithmetic expressions with project lemmas",
        ),
        (
            "decide",
            super::decide,
            "Solve decidable propositions by computation",
        ),
        (
            "simp",
            |ps| super::simp(ps, super::SimpConfig::default()),
            "Simplify the goal using simp lemmas",
        ),
        ("norm_num", super::norm_num, "Normalize numeric expressions"),
        (
            "ring",
            super::ring,
            "Prove equalities in commutative (semi)rings",
        ),
        (
            "linarith",
            super::linarith,
            "Prove linear arithmetic inequalities",
        ),
        (
            "tauto",
            super::tauto,
            "Prove tautologies in propositional logic",
        ),
        (
            "aesop",
            super::aesop,
            "Automated proof search using extensible rule sets",
        ),
        (
            "nn_verify",
            super::nn_verify,
            "Domain-specific automation for neural network verification proofs",
        ),
    ];

    for &(name, handler, desc) in nullary_builtins {
        reg.register(name, move |_args, ps| handler(ps), desc);
    }
}

/// Register built-in tactics that take arguments.
fn register_arg_builtins(reg: &mut UserTacticRegistry) {
    // exact: provide an exact proof term
    reg.register(
        "exact",
        |_args, _ps| {
            Err(TacticError::MissingArgument {
                tactic: "exact".into(),
                expected: "a proof term (use internal dispatch for elaborated args)".into(),
            })
        },
        "Provide an exact proof term for the current goal",
    );

    // apply: apply a term to produce subgoals
    reg.register(
        "apply",
        |_args, _ps| {
            Err(TacticError::MissingArgument {
                tactic: "apply".into(),
                expected: "a term to apply (use internal dispatch for elaborated args)".into(),
            })
        },
        "Apply a function or lemma, creating subgoals for its arguments",
    );

    // cases: perform case analysis on a hypothesis
    reg.register(
        "cases",
        |_args, _ps| {
            Err(TacticError::MissingArgument {
                tactic: "cases".into(),
                expected: "a hypothesis name (use internal dispatch for elaborated args)".into(),
            })
        },
        "Perform case analysis on a term of an inductive type",
    );

    // induction: perform induction on a variable
    reg.register(
        "induction",
        |_args, _ps| {
            Err(TacticError::MissingArgument {
                tactic: "induction".into(),
                expected: "a variable name (use internal dispatch for elaborated args)".into(),
            })
        },
        "Perform structural induction on a variable",
    );

    // monad_pres: compositional state-field preservation (#3403)
    reg.register(
        "monad_pres",
        |_args, _ps| {
            Err(TacticError::MissingArgument {
                tactic: "monad_pres".into(),
                expected: "field names (use internal dispatch for elaborated args)".into(),
            })
        },
        "Prove state-field preservation through monadic bind chains",
    );
}

#[cfg(test)]
#[path = "tactic_registry_tests.rs"]
mod tests;
