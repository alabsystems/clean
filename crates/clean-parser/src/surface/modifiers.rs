// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Declaration modifiers: visibility, partiality, computability, and scope.
//!
//! In Lean 4, declarations can be preceded by modifiers like `private`,
//! `protected`, `partial`, `noncomputable`, `scoped`, and `local`.
//! These were previously parsed and discarded; this module stores them
//! in the AST for downstream elaboration.

/// Visibility of a declaration.
///
/// Controls name resolution: whether the declaration is accessible
/// outside its namespace.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum Visibility {
    /// Default: fully accessible (no modifier or explicit `public`)
    #[default]
    Public,
    /// `protected`: accessible only via full qualified name outside namespace
    Protected,
    /// `private`: not accessible outside the current file/section
    Private,
}

/// Scope of a declaration within the current namespace context.
///
/// Controls whether notations and attributes propagated by this
/// declaration are limited to `open` context or local section scope.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum DeclScope {
    /// Default: normal scoping rules
    #[default]
    Default,
    /// `scoped`: notation/attribute only active when namespace is `open`ed
    Scoped,
    /// `local`: notation/attribute only active in current section/file
    Local,
}

/// Collected declaration modifiers parsed before a declaration keyword.
///
/// Lean 4 allows modifiers like `private partial def ...` or
/// `noncomputable protected def ...`. These are accumulated into
/// this struct and attached to the resulting `SurfaceDecl`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub struct DeclModifiers {
    /// Visibility: public (default), protected, or private
    pub visibility: Visibility,
    /// Whether the definition is `partial` (allowed to be non-terminating)
    pub is_partial: bool,
    /// Whether the definition is `noncomputable` (no code generation)
    pub is_noncomputable: bool,
    /// Whether the definition is `unsafe`
    pub is_unsafe: bool,
    /// Scope: default, scoped, or local
    pub scope: DeclScope,
    /// Whether this is an `abbrev` declaration (marked `@[reducible]` in Lean 4).
    ///
    /// In Lean 4, `abbrev` creates a definition with `ReducibilityHints.Abbreviation`,
    /// meaning it is always unfolded during definitional equality checking. Regular
    /// `def` creates `ReducibilityHints.Regular(height)`, which is only unfolded when
    /// both sides have the same head or during the lazy delta loop.
    ///
    /// Part of #3391: without this flag, `abbrev Sem (a : Type) := StateT Nat (Except SemError) a`
    /// is not reduced during type elaboration, causing type mismatches.
    pub is_abbrev: bool,
}

impl DeclModifiers {
    /// Returns `true` if all modifier fields are at their default values.
    #[must_use]
    pub fn is_default(&self) -> bool {
        self.visibility == Visibility::Public
            && !self.is_partial
            && !self.is_noncomputable
            && !self.is_unsafe
            && !self.is_abbrev
            && self.scope == DeclScope::Default
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_modifiers_default_values() {
        let m = DeclModifiers::default();
        assert_eq!(m.visibility, Visibility::Public);
        assert!(!m.is_partial);
        assert!(!m.is_noncomputable);
        assert!(!m.is_unsafe);
        assert!(!m.is_abbrev);
        assert_eq!(m.scope, DeclScope::Default);
    }

    #[test]
    fn test_modifiers_is_default_true() {
        let m = DeclModifiers::default();
        assert!(m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_visibility_private() {
        let m = DeclModifiers {
            visibility: Visibility::Private,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_visibility_protected() {
        let m = DeclModifiers {
            visibility: Visibility::Protected,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_partial() {
        let m = DeclModifiers {
            is_partial: true,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_noncomputable() {
        let m = DeclModifiers {
            is_noncomputable: true,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_unsafe() {
        let m = DeclModifiers {
            is_unsafe: true,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_scoped() {
        let m = DeclModifiers {
            scope: DeclScope::Scoped,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_local() {
        let m = DeclModifiers {
            scope: DeclScope::Local,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_is_default_false_abbrev() {
        let m = DeclModifiers {
            is_abbrev: true,
            ..Default::default()
        };
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_combination_private_partial() {
        let m = DeclModifiers {
            visibility: Visibility::Private,
            is_partial: true,
            ..Default::default()
        };
        assert_eq!(m.visibility, Visibility::Private);
        assert!(m.is_partial);
        assert!(!m.is_noncomputable);
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_combination_protected_noncomputable_scoped() {
        let m = DeclModifiers {
            visibility: Visibility::Protected,
            is_noncomputable: true,
            scope: DeclScope::Scoped,
            ..Default::default()
        };
        assert_eq!(m.visibility, Visibility::Protected);
        assert!(m.is_noncomputable);
        assert_eq!(m.scope, DeclScope::Scoped);
        assert!(!m.is_default());
    }

    #[test]
    fn test_modifiers_all_set() {
        let m = DeclModifiers {
            visibility: Visibility::Private,
            is_partial: true,
            is_noncomputable: true,
            is_unsafe: true,
            is_abbrev: true,
            scope: DeclScope::Local,
        };
        assert!(!m.is_default());
        assert_eq!(m.visibility, Visibility::Private);
        assert!(m.is_partial);
        assert!(m.is_noncomputable);
        assert!(m.is_unsafe);
        assert!(m.is_abbrev);
        assert_eq!(m.scope, DeclScope::Local);
    }

    #[test]
    fn test_visibility_default() {
        assert_eq!(Visibility::default(), Visibility::Public);
    }

    #[test]
    fn test_decl_scope_default() {
        assert_eq!(DeclScope::default(), DeclScope::Default);
    }

    #[test]
    fn test_modifiers_clone_eq() {
        let m = DeclModifiers {
            visibility: Visibility::Protected,
            is_partial: true,
            ..Default::default()
        };
        let m2 = m;
        assert_eq!(m, m2);
    }
}
