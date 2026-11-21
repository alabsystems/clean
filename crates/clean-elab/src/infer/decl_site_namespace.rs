// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The namespace pinned Lean opens around a declaration, computed from the
//! name as WRITTEN (`Lean/Elab/Declaration.lean@v4.30.0-rc2`):
//!
//! * `expandDeclNamespace?`: a declaration written `pre.short` with `pre`
//!   non-anonymous is elaborated as `namespace pre` + `short`, whatever its
//!   modifiers, so `private def N.d` opens `N`; a name with a `_root_` prefix
//!   opens nothing, and so does a one-component one (or a nameless instance);
//! * `expandMutualNamespace`: a `mutual` block opens the common component
//!   prefix of its members' namespaces, and nothing when a member has none or
//!   the prefix is anonymous. Every member's attributes resolve in it.
//!
//! The kernel name cannot answer this: `private def N.d` is
//! `_private.<module>.0.N.d`, and `def _root_.N.d` written at the root is
//! `N.d`, the same kernel name as `def N.d`.

use clean_kernel::name::{Name, NameInner};
use clean_parser::{SurfaceDecl, SurfaceName};

use super::elaborate_decl::DeclaredSurfaceName;
use super::ElabCtx;

/// The namespace `expandDeclNamespace?` opens for a name written `written`,
/// relative to the current one.
fn written_namespace(written: &SurfaceName) -> Option<Name> {
    let name = written.name();
    if first_component(name) == Some("_root_") {
        return None;
    }
    match name.inner() {
        NameInner::Str(pre, _) if !pre.is_anon() => Some(pre.as_ref().clone()),
        _ => None,
    }
}

/// The text of `name`'s first component, when it is a string.
fn first_component(name: &Name) -> Option<&str> {
    let mut current = name;
    let mut first = None;
    loop {
        match current.inner() {
            NameInner::Anon => return first,
            NameInner::Str(parent, text) => {
                first = Some(text.as_ref());
                current = parent;
            }
            NameInner::Num(parent, _) => {
                first = None;
                current = parent;
            }
        }
    }
}

/// Every non-anonymous prefix of `name`, shortest first.
fn prefixes(name: &Name) -> Vec<Name> {
    let mut chain = Vec::new();
    let mut current = name.clone();
    while !current.is_anon() {
        let parent = crate::namespace::parent_name(&current);
        chain.push(current);
        current = parent;
    }
    chain.reverse();
    chain
}

/// Lean's `findCommonPrefix` of two names: their longest common component
/// prefix.
fn common_prefix(a: &Name, b: &Name) -> Name {
    prefixes(a)
        .into_iter()
        .zip(prefixes(b))
        .take_while(|(x, y)| x == y)
        .last()
        .map_or_else(Name::anon, |(x, _)| x)
}

impl ElabCtx<'_> {
    /// Namespace for looking up a written term or pattern. Template references
    /// retain their definition site. A qualified declaration enters its
    /// written namespace for its signature and body.
    pub(super) fn term_lookup_namespace(&self, name: &SurfaceName) -> SurfaceName {
        if let Some(origin) = name.template_origin() {
            return SurfaceName::from_name(origin.namespace.clone());
        }
        match &self.decl_site_namespace {
            Some(namespace) => SurfaceName::from_name(namespace.clone()),
            None => self.namespace_prefix.clone(),
        }
    }

    /// The full namespace pinned Lean opens around `decl` (module doc), or
    /// `None` when it opens none.
    pub(super) fn lean_decl_namespace(&self, decl: &SurfaceDecl) -> Option<Name> {
        let opened = match Self::declared_surface_name(decl) {
            DeclaredSurfaceName::One(written) => written_namespace(written)?,
            DeclaredSurfaceName::Block(members) => {
                let mut common: Option<Name> = None;
                for member in members {
                    let DeclaredSurfaceName::One(written) = Self::declared_surface_name(member)
                    else {
                        return None;
                    };
                    let namespace = written_namespace(written)?;
                    common = Some(match common {
                        None => namespace,
                        Some(common) => common_prefix(&common, &namespace),
                    });
                }
                common.filter(|common| !common.is_anon())?
            }
            DeclaredSurfaceName::None => return None,
        };
        Some(crate::namespace::append_names(
            self.namespace_state.current_namespace(),
            &opened,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn written(path: &str) -> SurfaceName {
        SurfaceName::from_name(Name::from_string(path))
    }

    #[test]
    fn test_written_namespace_follows_expand_decl_namespace() {
        assert_eq!(
            written_namespace(&written("N.d")),
            Some(Name::from_string("N"))
        );
        assert_eq!(
            written_namespace(&written("A.B.d")),
            Some(Name::from_string("A.B"))
        );
        assert_eq!(written_namespace(&written("d")), None);
        assert_eq!(written_namespace(&written("_root_.N.d")), None);
        assert_eq!(written_namespace(&written("_root_.d")), None);
    }

    #[test]
    fn qualified_declaration_resolves_terms_and_constructor_patterns_at_its_site() {
        use crate::test_support::file_verdicts::{
            assert_all_accepted, run_modules_env_messages, verdict_of,
        };

        let family = "inductive Tree where\n  | leaf\n  | node (child : Tree)\n";
        let accepted = format!(
            "{family}{}",
            r#"
def Tree.tag (tree : Tree) : Nat :=
  match tree with
  | leaf => 12
  | node _ => 35
def Tree.byName : Tree := leaf
def Tree.throughLocal (leaf : Nat) := leaf
theorem firstTag : Tree.tag Tree.byName = 12 := rfl
theorem secondTag : Tree.tag (.node .leaf) = 35 := rfl
theorem localWins : Tree.throughLocal 81 = 81 := rfl
"#
        );
        let (_, results) = run_modules_env_messages(&[&accepted]);
        assert_all_accepted(&results, &accepted);

        // A root escape suppresses the implicit namespace even though both
        // spellings define constants under Tree in the environment.
        let escaped = format!("{family}def _root_.Tree.byName : Tree := leaf\n");
        let (_, results) = run_modules_env_messages(&[&escaped]);
        assert!(verdict_of(&results, "Tree.byName").is_err(), "{results:?}");
    }

    #[test]
    fn test_common_prefix_is_componentwise() {
        let common = |a: &str, b: &str| common_prefix(&Name::from_string(a), &Name::from_string(b));
        assert_eq!(common("N.A", "N.B"), Name::from_string("N"));
        assert_eq!(common("N.A", "N.A"), Name::from_string("N.A"));
        assert_eq!(common("N", "M"), Name::anon());
        assert_eq!(common("Nat", "N"), Name::anon());
    }
}
