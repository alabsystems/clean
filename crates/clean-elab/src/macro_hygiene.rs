// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Hygiene tracking for macro expansion in the clean elaborator.
//!
//! This module records macro scopes, tracks which names were introduced in each
//! scope, and resolves names against the currently active macro-expansion stack.

use std::collections::HashMap;
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct MacroScope(u64);

impl MacroScope {
    #[must_use]
    pub(crate) fn root() -> Self {
        Self(0)
    }

    #[must_use]
    pub(crate) fn id(self) -> u64 {
        self.0
    }

    #[must_use]
    pub(crate) fn is_root(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Display for MacroScope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "MacroScope({})", self.0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct HygienicName {
    pub(crate) raw_name: String,
    pub(crate) scope: MacroScope,
    pub(crate) is_gensym: bool,
}

impl fmt::Display for HygienicName {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_gensym {
            write!(f, "{} [{}; gensym]", self.raw_name, self.scope)
        } else {
            write!(f, "{} [{}]", self.raw_name, self.scope)
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub(crate) enum HygieneResolution {
    Resolved(HygienicName),
    Ambiguous(Vec<HygienicName>),
    Unresolved,
}

impl fmt::Display for HygieneResolution {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Resolved(name) => write!(f, "Resolved({name})"),
            Self::Ambiguous(names) => {
                write!(f, "Ambiguous(")?;
                for (index, name) in names.iter().enumerate() {
                    if index > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{name}")?;
                }
                write!(f, ")")
            }
            Self::Unresolved => f.write_str("Unresolved"),
        }
    }
}

pub(crate) struct HygieneCtx {
    next_scope: u64,
    scope_stack: Vec<MacroScope>,
    name_scopes: HashMap<String, Vec<MacroScope>>,
    gensym_counter: u64,
}

impl Default for HygieneCtx {
    fn default() -> Self {
        Self::new()
    }
}

impl HygieneCtx {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self {
            next_scope: 1,
            scope_stack: vec![MacroScope::root()],
            name_scopes: HashMap::new(),
            gensym_counter: 0,
        }
    }

    pub(crate) fn fresh_scope(&mut self) -> MacroScope {
        let scope = MacroScope(self.next_scope);
        self.next_scope = self.next_scope.saturating_add(1);
        scope
    }

    pub(crate) fn push_scope(&mut self, scope: MacroScope) {
        self.scope_stack.push(scope);
    }

    pub(crate) fn pop_scope(&mut self) -> Option<MacroScope> {
        if self.scope_stack.len() <= 1 {
            None
        } else {
            self.scope_stack.pop()
        }
    }

    #[must_use]
    pub(crate) fn current_scope(&self) -> MacroScope {
        if let Some(scope) = self.scope_stack.last().copied() {
            scope
        } else {
            MacroScope::root()
        }
    }

    pub(crate) fn introduce_name(&mut self, name: &str, scope: MacroScope) {
        let scopes = self.name_scopes.entry(name.to_owned()).or_default();
        if !scopes.contains(&scope) {
            scopes.push(scope);
        }
    }

    #[must_use]
    pub(crate) fn resolve_name(&self, name: &str) -> HygieneResolution {
        let Some(registered_scopes) = self.name_scopes.get(name) else {
            return HygieneResolution::Unresolved;
        };

        let visible_scopes = self.visible_scopes_for(registered_scopes);
        match visible_scopes.as_slice() {
            [] => HygieneResolution::Unresolved,
            [scope] => HygieneResolution::Resolved(HygienicName {
                raw_name: name.to_owned(),
                scope: *scope,
                is_gensym: false,
            }),
            scopes => HygieneResolution::Ambiguous(
                scopes
                    .iter()
                    .copied()
                    .map(|scope| HygienicName {
                        raw_name: name.to_owned(),
                        scope,
                        is_gensym: false,
                    })
                    .collect(),
            ),
        }
    }

    pub(crate) fn gensym(&mut self, prefix: &str) -> HygienicName {
        let name = format!("{prefix}_hygiene_{}", self.gensym_counter);
        self.gensym_counter = self.gensym_counter.saturating_add(1);

        let scope = self.current_scope();
        self.introduce_name(&name, scope);

        HygienicName {
            raw_name: name,
            scope,
            is_gensym: true,
        }
    }

    #[must_use]
    pub(crate) fn is_visible(&self, name: &str, scope: MacroScope) -> bool {
        self.name_scopes
            .get(name)
            .is_some_and(|scopes| scopes.contains(&scope))
    }

    #[must_use]
    pub(crate) fn rename_for_hygiene(&self, name: &str) -> String {
        let Some(registered_scopes) = self.name_scopes.get(name) else {
            return name.to_owned();
        };

        let visible_scopes = self.visible_scopes_for(registered_scopes);
        if let Some(scope) = visible_scopes.last().copied() {
            format!("{name}_{}", scope.id())
        } else {
            name.to_owned()
        }
    }

    #[must_use]
    pub(crate) fn scope_depth(&self) -> usize {
        self.scope_stack.len()
    }

    #[must_use]
    pub(crate) fn all_scopes(&self) -> &[MacroScope] {
        &self.scope_stack
    }

    #[must_use]
    pub(crate) fn names_in_scope(&self, scope: MacroScope) -> Vec<String> {
        let mut names = self
            .name_scopes
            .iter()
            .filter_map(|(name, scopes)| {
                if scopes.contains(&scope) {
                    Some(name.clone())
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        names.sort_unstable();
        names
    }

    fn visible_scopes_for(&self, registered_scopes: &[MacroScope]) -> Vec<MacroScope> {
        let mut visible_scopes = Vec::new();
        for scope in &self.scope_stack {
            if registered_scopes.contains(scope) && !visible_scopes.contains(scope) {
                visible_scopes.push(*scope);
            }
        }
        visible_scopes
    }
}
