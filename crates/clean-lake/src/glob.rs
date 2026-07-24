// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lake module-glob matching.
//!
//! A `lean_lib` target may declare `globs := #[...]` to partition the modules
//! of a package across library targets. This module parses each glob spec into
//! a [`ModuleGlob`] and matches candidate module names against it.
//!
//! Lake supports three glob forms (see `Lake.Glob` upstream):
//!
//! - `.one Mod` — exactly the module `Mod`.
//! - `.andSubmodules Mod` — `Mod` together with every submodule `Mod.*`.
//! - `.submodules Mod` — every submodule `Mod.*`, but **not** `Mod` itself.
//!
//! Module names are dot-separated (`Foo.Bar.Baz`); a submodule relationship is
//! decided on dot boundaries so that `Foo` is a prefix of `Foo.Bar` but never
//! of an unrelated module such as `FooBar`.

/// The kind of a parsed module glob.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlobKind {
    /// `.one Mod` — matches exactly `Mod`.
    One,
    /// `.andSubmodules Mod` — matches `Mod` and every submodule `Mod.*`.
    AndSubmodules,
    /// `.submodules Mod` — matches every submodule `Mod.*`, not `Mod` itself.
    Submodules,
}

/// A parsed Lake module glob: a base module name plus a match kind.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ModuleGlob {
    /// Base module name (dot-separated, backticks stripped).
    pub module: String,
    /// How candidate modules are matched against [`Self::module`].
    pub kind: GlobKind,
}

impl ModuleGlob {
    /// Parse a single glob spec string into a [`ModuleGlob`].
    ///
    /// Accepts the spellings produced by the lakefile parser, e.g.
    /// `` .submodules `Foo ``, `.andSubmodules Foo`, `.one Foo`, as well as a
    /// bare module name (treated as `.andSubmodules`, matching Lake's default
    /// glob for a root). Surrounding whitespace and a leading name backtick are
    /// tolerated. Returns `None` for an empty or unrecognized spec.
    #[must_use]
    pub fn parse(spec: &str) -> Option<Self> {
        let spec = spec.trim();
        if spec.is_empty() {
            return None;
        }

        let (kind, rest) = if let Some(rest) = spec.strip_prefix(".andSubmodules") {
            (GlobKind::AndSubmodules, rest)
        } else if let Some(rest) = spec.strip_prefix(".submodules") {
            (GlobKind::Submodules, rest)
        } else if let Some(rest) = spec.strip_prefix(".one") {
            (GlobKind::One, rest)
        } else {
            // Bare module name: Lake's default glob for a root is
            // `.andSubmodules`, so mirror that here.
            (GlobKind::AndSubmodules, spec)
        };

        let module = Self::clean_module_name(rest);
        if module.is_empty() {
            return None;
        }

        Some(Self { module, kind })
    }

    /// Normalize a raw module token: drop surrounding whitespace and a single
    /// leading name backtick (Lean name-literal syntax, e.g. `` `Foo ``).
    fn clean_module_name(raw: &str) -> String {
        raw.trim().trim_start_matches('`').trim().to_string()
    }

    /// Test whether `candidate` (a dot-separated module name) matches this glob.
    #[must_use]
    pub fn matches(&self, candidate: &str) -> bool {
        match self.kind {
            GlobKind::One => candidate == self.module,
            GlobKind::AndSubmodules => {
                candidate == self.module || is_submodule_of(candidate, &self.module)
            }
            GlobKind::Submodules => is_submodule_of(candidate, &self.module),
        }
    }
}

/// Whether `candidate` is a strict submodule of `base`, i.e. `base.<something>`.
///
/// The relationship is decided on dot boundaries: `Foo` is a base of `Foo.Bar`
/// but not of `FooBar`.
fn is_submodule_of(candidate: &str, base: &str) -> bool {
    candidate
        .strip_prefix(base)
        .is_some_and(|rest| rest.starts_with('.') && rest.len() > 1)
}

/// Parse a list of glob spec strings, discarding any that are empty or
/// unrecognized.
#[must_use]
pub fn parse_globs(specs: &[String]) -> Vec<ModuleGlob> {
    specs.iter().filter_map(|s| ModuleGlob::parse(s)).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_submodules_with_backtick() {
        let glob = ModuleGlob::parse(".submodules `Foo").expect("should parse");
        assert_eq!(glob.module, "Foo");
        assert_eq!(glob.kind, GlobKind::Submodules);
    }

    #[test]
    fn test_parse_and_submodules() {
        let glob = ModuleGlob::parse(".andSubmodules Foo").expect("should parse");
        assert_eq!(glob.module, "Foo");
        assert_eq!(glob.kind, GlobKind::AndSubmodules);
    }

    #[test]
    fn test_parse_one() {
        let glob = ModuleGlob::parse(".one `Foo").expect("should parse");
        assert_eq!(glob.module, "Foo");
        assert_eq!(glob.kind, GlobKind::One);
    }

    #[test]
    fn test_parse_bare_name_is_and_submodules() {
        let glob = ModuleGlob::parse("`Foo").expect("should parse");
        assert_eq!(glob.module, "Foo");
        assert_eq!(glob.kind, GlobKind::AndSubmodules);
    }

    #[test]
    fn test_parse_empty_returns_none() {
        assert!(ModuleGlob::parse("").is_none());
        assert!(ModuleGlob::parse("   ").is_none());
        assert!(ModuleGlob::parse(".submodules").is_none());
    }

    #[test]
    fn test_one_matches_only_exact() {
        let glob = ModuleGlob {
            module: "Foo".to_string(),
            kind: GlobKind::One,
        };
        assert!(glob.matches("Foo"));
        assert!(!glob.matches("Foo.Bar"));
        assert!(!glob.matches("FooBar"));
        assert!(!glob.matches("Qux"));
    }

    #[test]
    fn test_submodules_matches_children_not_self() {
        let glob = ModuleGlob {
            module: "Foo".to_string(),
            kind: GlobKind::Submodules,
        };
        assert!(!glob.matches("Foo"));
        assert!(glob.matches("Foo.Bar"));
        assert!(glob.matches("Foo.Baz"));
        assert!(glob.matches("Foo.Bar.Deep"));
        assert!(!glob.matches("FooBar"));
        assert!(!glob.matches("Qux"));
    }

    #[test]
    fn test_and_submodules_matches_self_and_children() {
        let glob = ModuleGlob {
            module: "Foo".to_string(),
            kind: GlobKind::AndSubmodules,
        };
        assert!(glob.matches("Foo"));
        assert!(glob.matches("Foo.Bar"));
        assert!(!glob.matches("FooBar"));
        assert!(!glob.matches("Qux"));
    }

    #[test]
    fn test_is_submodule_of_dot_boundary() {
        assert!(is_submodule_of("Foo.Bar", "Foo"));
        assert!(is_submodule_of("Foo.Bar.Baz", "Foo"));
        assert!(!is_submodule_of("FooBar", "Foo"));
        assert!(!is_submodule_of("Foo", "Foo"));
        assert!(!is_submodule_of("Foo.", "Foo"));
    }
}
