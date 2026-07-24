// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Variable interpolation for lakefile configuration values.
//!
//! Lakefiles frequently parameterize configuration with variables — the package
//! name, the workspace directory, or values pulled from the environment. This
//! module expands those references at config-load time so the rest of the
//! pipeline never sees an unexpanded `$(VAR)`.
//!
//! ## Syntax
//!
//! Two equivalent reference forms are recognized inside string values:
//!
//! - `$(NAME)` — parenthesized (Make / Lake convention)
//! - `${NAME}` — braced (shell convention)
//!
//! A literal dollar sign is written as `$$`. Names may contain ASCII letters,
//! digits, and underscores.
//!
//! ## Resolution
//!
//! References resolve against an explicit [`InterpContext`] first (built-in
//! variables such as the package name and directory), then fall back to process
//! environment variables. Context values may themselves contain references and
//! are expanded recursively; a [`CyclicVariable`](crate::LakeError::CyclicVariable)
//! error is raised if the references form a cycle. An unresolved name yields an
//! [`UnknownVariable`](crate::LakeError::UnknownVariable) error rather than
//! silently expanding to the empty string.

use crate::error::{LakeError, LakeResult};
use std::collections::HashMap;

/// Variables available to lakefile interpolation, layered over the process
/// environment.
///
/// Names registered here shadow environment variables of the same name. Values
/// may reference other variables; they are expanded lazily with cycle
/// detection.
#[derive(Debug, Clone, Default)]
pub(crate) struct InterpContext {
    vars: HashMap<String, String>,
    /// When `true`, fall back to process environment variables for names not
    /// found in `vars`. Disabled in tests that must stay hermetic.
    use_env: bool,
}

impl InterpContext {
    /// Create an empty context that falls back to the process environment.
    pub(crate) fn new() -> Self {
        Self {
            vars: HashMap::new(),
            use_env: true,
        }
    }

    /// Register (or overwrite) a variable binding.
    pub(crate) fn set(&mut self, name: impl Into<String>, value: impl Into<String>) {
        self.vars.insert(name.into(), value.into());
    }

    /// Disable environment fallback (used to keep tests hermetic).
    #[cfg(test)]
    pub(crate) fn without_env(mut self) -> Self {
        self.use_env = false;
        self
    }

    /// Look up the raw (unexpanded) value bound to `name`.
    fn lookup(&self, name: &str) -> Option<String> {
        if let Some(value) = self.vars.get(name) {
            return Some(value.clone());
        }
        if self.use_env {
            if let Ok(value) = std::env::var(name) {
                return Some(value);
            }
        }
        None
    }

    /// Expand every variable reference in `input`, returning the resolved
    /// string. Returns an error on unknown names, unterminated references, or
    /// reference cycles.
    pub(crate) fn expand(&self, input: &str) -> LakeResult<String> {
        let mut active = Vec::new();
        self.expand_inner(input, &mut active)
    }

    fn expand_inner(&self, input: &str, active: &mut Vec<String>) -> LakeResult<String> {
        let mut out = String::with_capacity(input.len());
        let mut chars = input.char_indices().peekable();

        while let Some((_, ch)) = chars.next() {
            if ch != '$' {
                out.push(ch);
                continue;
            }

            match chars.peek().map(|&(_, c)| c) {
                // Escaped literal dollar: `$$` -> `$`.
                Some('$') => {
                    chars.next();
                    out.push('$');
                }
                Some('(') => {
                    chars.next();
                    let name = read_name(&mut chars, ')', input)?;
                    out.push_str(&self.resolve(&name, active)?);
                }
                Some('{') => {
                    chars.next();
                    let name = read_name(&mut chars, '}', input)?;
                    out.push_str(&self.resolve(&name, active)?);
                }
                // A lone `$` not introducing a reference is preserved verbatim.
                _ => out.push('$'),
            }
        }

        Ok(out)
    }

    /// Resolve a single variable name, recursively expanding its value while
    /// guarding against cycles.
    fn resolve(&self, name: &str, active: &mut Vec<String>) -> LakeResult<String> {
        if active.iter().any(|n| n == name) {
            return Err(LakeError::CyclicVariable {
                name: name.to_string(),
            });
        }
        let raw = self
            .lookup(name)
            .ok_or_else(|| LakeError::UnknownVariable {
                name: name.to_string(),
                value: format!("$({name})"),
            })?;

        active.push(name.to_string());
        let expanded = self.expand_inner(&raw, active);
        active.pop();
        expanded
    }
}

/// Read a variable name up to (and consuming) the `close` delimiter.
fn read_name<I>(chars: &mut std::iter::Peekable<I>, close: char, input: &str) -> LakeResult<String>
where
    I: Iterator<Item = (usize, char)>,
{
    let mut name = String::new();
    for (_, c) in chars.by_ref() {
        if c == close {
            return Ok(name);
        }
        name.push(c);
    }
    Err(LakeError::UnterminatedVariable {
        value: input.to_string(),
    })
}

/// Returns `true` if `input` contains at least one (non-escaped) variable
/// reference, so callers can skip the expansion pass for plain strings.
pub(crate) fn contains_reference(input: &str) -> bool {
    let mut chars = input.char_indices().peekable();
    while let Some((_, ch)) = chars.next() {
        if ch != '$' {
            continue;
        }
        match chars.peek().map(|&(_, c)| c) {
            Some('$') => {
                chars.next();
            }
            Some('(') | Some('{') => return true,
            _ => {}
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ctx() -> InterpContext {
        let mut c = InterpContext::new().without_env();
        c.set("PKG", "demo");
        c.set("DIR", "/work/demo");
        c
    }

    #[test]
    fn test_expand_no_reference_is_identity() {
        let c = ctx();
        assert_eq!(c.expand("plain string").unwrap(), "plain string");
    }

    #[test]
    fn test_expand_paren_reference_resolves() {
        let c = ctx();
        assert_eq!(c.expand("name-$(PKG)").unwrap(), "name-demo");
    }

    #[test]
    fn test_expand_brace_reference_resolves() {
        let c = ctx();
        assert_eq!(c.expand("${DIR}/build").unwrap(), "/work/demo/build");
    }

    #[test]
    fn test_expand_multiple_references_resolve() {
        let c = ctx();
        assert_eq!(c.expand("$(PKG)@$(DIR)").unwrap(), "demo@/work/demo");
    }

    #[test]
    fn test_expand_escaped_dollar_is_literal() {
        let c = ctx();
        assert_eq!(
            c.expand("price is $$5 for $(PKG)").unwrap(),
            "price is $5 for demo"
        );
    }

    #[test]
    fn test_expand_lone_dollar_is_preserved() {
        let c = ctx();
        assert_eq!(c.expand("a $ b").unwrap(), "a $ b");
    }

    #[test]
    fn test_expand_unknown_variable_errors() {
        let c = ctx();
        let err = c.expand("$(MISSING)").unwrap_err();
        assert!(
            matches!(err, LakeError::UnknownVariable { ref name, .. } if name == "MISSING"),
            "expected UnknownVariable, got: {err:?}"
        );
    }

    #[test]
    fn test_expand_unterminated_reference_errors() {
        let c = ctx();
        let err = c.expand("$(PKG").unwrap_err();
        assert!(
            matches!(err, LakeError::UnterminatedVariable { .. }),
            "expected UnterminatedVariable, got: {err:?}"
        );
    }

    #[test]
    fn test_expand_nested_reference_resolves() {
        let mut c = InterpContext::new().without_env();
        c.set("BASE", "/opt");
        c.set("HOME_DIR", "$(BASE)/clean");
        assert_eq!(c.expand("$(HOME_DIR)/bin").unwrap(), "/opt/clean/bin");
    }

    #[test]
    fn test_expand_cyclic_reference_errors() {
        let mut c = InterpContext::new().without_env();
        c.set("A", "$(B)");
        c.set("B", "$(A)");
        let err = c.expand("$(A)").unwrap_err();
        assert!(
            matches!(err, LakeError::CyclicVariable { .. }),
            "expected CyclicVariable, got: {err:?}"
        );
    }

    #[test]
    fn test_expand_self_reference_errors() {
        let mut c = InterpContext::new().without_env();
        c.set("SELF", "x-$(SELF)");
        let err = c.expand("$(SELF)").unwrap_err();
        assert!(
            matches!(err, LakeError::CyclicVariable { ref name, .. } if name == "SELF"),
            "expected CyclicVariable for SELF, got: {err:?}"
        );
    }

    #[test]
    fn test_contains_reference_detects_forms() {
        assert!(contains_reference("a $(X) b"));
        assert!(contains_reference("a ${X} b"));
        assert!(!contains_reference("plain"));
        assert!(!contains_reference("escaped $$ only"));
        assert!(!contains_reference("lone $ sign"));
    }

    #[test]
    fn test_env_fallback_resolves() {
        // Hermetic: set a unique var on the process and resolve via fallback.
        let key = "CLEAN_LAKE_INTERP_TEST_VAR";
        let result = crate::test_env::with_serialized_env_vars(&[(key, "from-env")], || {
            let c = InterpContext::new();
            c.expand(&format!("v=$({key})"))
        });
        assert_eq!(result.unwrap(), "v=from-env");
    }
}
