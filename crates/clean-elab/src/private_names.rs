// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Lean's module-local `private` names (G21,
//! `designs/2026-10-08-private-name-mangling.md`).
//!
//! A port of Lean 4.8.0 `src/Lean/Modifiers.lean:32-88`. A `private`
//! declaration `n` of module `M` is registered as `_private.M.0.n`: two
//! sibling modules may then each declare a private `helper`, and an importer
//! of both holds two distinct constants, neither of which its plain name
//! reaches (Lean resolves `n` to `_private.<main module>.0.n` only inside the
//! module that declared it — `ResolveName.lean`'s "private step").
//!
//! [`mk_private_name`] strips a private prefix `n` already carries before
//! adding the module's (Lean v4.30's `PrivateName.lean:23-30` form); on a user
//! name, the only input the elaborator gives it, the result is 4.8.0's.

use clean_kernel::expr::LevelVec;
use clean_kernel::name::{Name, NameInner};
use clean_kernel::{Expr, ExprFolder};

/// `_private`, Lean's `privateHeader`.
pub const PRIVATE_HEADER: &str = "_private";

/// `_private.<module>.0`: the prefix every private name of `module` carries.
#[must_use]
pub(crate) fn private_prefix_of(module: &Name) -> Name {
    crate::namespace::append_names(&Name::anon().str(PRIVATE_HEADER), module).num(0)
}

/// Lean's `mkPrivateName`: `_private.<module>.0 ++ privateToUserName(n).getD n`.
#[must_use]
pub(crate) fn mk_private_name(module: &Name, name: &Name) -> Name {
    let user = private_to_user_name(name).unwrap_or_else(|| name.clone());
    crate::namespace::append_names(&private_prefix_of(module), &user)
}

/// [`mk_private_name`] over a prefix [`private_prefix_of`] already built.
#[must_use]
pub(crate) fn mk_private_name_with_prefix(prefix: &Name, name: &Name) -> Name {
    let user = private_to_user_name(name).unwrap_or_else(|| name.clone());
    crate::namespace::append_names(prefix, &user)
}

fn is_private_header(name: &Name) -> bool {
    match name.inner() {
        NameInner::Str(parent, text) => parent.is_anon() && text.as_ref() == PRIVATE_HEADER,
        NameInner::Anon | NameInner::Num(..) => false,
    }
}

/// Lean's `isPrivateName`: some prefix of `name` is `_private`.
#[must_use]
pub(crate) fn is_private_name(name: &Name) -> bool {
    let mut current = name;
    loop {
        if is_private_header(current) {
            return true;
        }
        match current.inner() {
            NameInner::Anon => return false,
            NameInner::Str(parent, _) | NameInner::Num(parent, _) => current = parent,
        }
    }
}

/// Lean's `isPrivatePrefix`: `name` is exactly `_private.<module>.0`, with a
/// module made of string components only.
#[must_use]
pub(crate) fn is_private_prefix(name: &Name) -> bool {
    let NameInner::Num(parent, 0) = name.inner() else {
        return false;
    };
    let mut current: &Name = parent;
    loop {
        if is_private_header(current) {
            return true;
        }
        match current.inner() {
            NameInner::Str(parent, _) => current = parent,
            NameInner::Anon | NameInner::Num(..) => return false,
        }
    }
}

/// Lean's `privateToUserNameAux`.
fn private_to_user_name_aux(name: &Name) -> Name {
    match name.inner() {
        NameInner::Str(parent, text) => private_to_user_name_aux(parent).str(text.as_ref()),
        NameInner::Num(parent, number) => {
            if is_private_prefix(name) {
                Name::anon()
            } else {
                private_to_user_name_aux(parent).num(*number)
            }
        }
        NameInner::Anon => Name::anon(),
    }
}

/// Lean's `privateToUserName?`: the user-facing name of a private name
/// (`_private.Pkg.A.0.Foo.helper` ↦ `Foo.helper`), `None` for any other.
#[must_use]
pub(crate) fn private_to_user_name(name: &Name) -> Option<Name> {
    is_private_name(name).then(|| private_to_user_name_aux(name))
}

/// The user-facing spelling of a declaration name: the user name of a private
/// one, the name itself otherwise. For labels and messages ONLY — a name
/// string is a map key elsewhere, and two siblings' `helper` would collide.
#[must_use]
pub fn user_facing_name(name: &Name) -> Name {
    private_to_user_name(name).unwrap_or_else(|| name.clone())
}

/// A copy of `expr` in which every private constant carries its user-facing
/// name, for RENDERING only: Lean 4.8.0's delaborator prints `pd 1 = 2` for
/// a private `pd` (`#check pt` shows `pt : pd 1 = 2`). Never hand the result
/// to the kernel or use it as a key — two siblings' `pd` become one name.
pub fn user_facing_expr(expr: &Expr) -> Expr {
    struct UserFacing;
    impl ExprFolder for UserFacing {
        fn fold_const(&mut self, name: &Name, levels: &LevelVec) -> Expr {
            Expr::const_(user_facing_name(name), levels.clone())
        }
    }
    UserFacing.fold_expr(expr)
}

/// `text` with every private name it spells (`_private.<module>.0.<rest>`)
/// written as its user-facing name, for a message whose terms were already
/// rendered to text (a kernel type error's `has type …`). Lean 4.8.0 prints
/// `pd 1 = 2` there for a private `pd`. A `_private.` occurrence that does not
/// spell a private prefix (no numeric `0` component after a module) is left
/// as written. RENDERING only, as [`user_facing_expr`].
#[must_use]
pub(crate) fn user_facing_text(text: &str) -> String {
    const HEADER: &str = "_private.";
    let mut out = String::with_capacity(text.len());
    let mut rest = text;
    while let Some(at) = rest.find(HEADER) {
        let boundary = rest[..at]
            .chars()
            .next_back()
            .is_none_or(|c| !(c.is_alphanumeric() || c == '_' || c == '.' || c == '»'));
        let after = &rest[at + HEADER.len()..];
        match private_prefix_len(after).filter(|_| boundary) {
            Some(len) => {
                out.push_str(&rest[..at]);
                rest = &after[len..];
            }
            None => {
                out.push_str(&rest[..at + HEADER.len()]);
                rest = after;
            }
        }
    }
    out.push_str(rest);
    out
}

/// The length of `<module>.0.` at the start of `text` (the part of a private
/// prefix after `_private.`): one or more module components, each a plain
/// run or a `«…»` escape, then the numeric component `0` and a dot.
fn private_prefix_len(text: &str) -> Option<usize> {
    let mut pos = 0;
    let mut components = 0usize;
    loop {
        let tail = &text[pos..];
        let len = if let Some(escaped) = tail.strip_prefix('«') {
            escaped.find('»')? + '«'.len_utf8() + '»'.len_utf8()
        } else {
            tail.find(|c: char| {
                !(c.is_alphanumeric() || c == '_' || c == '\'' || c == '!' || c == '?')
            })
            .unwrap_or(tail.len())
        };
        if len == 0 {
            return None;
        }
        let component = &tail[..len];
        pos += len;
        if !text[pos..].starts_with('.') {
            return None;
        }
        pos += 1;
        if component == "0" && components > 0 {
            return Some(pos);
        }
        components += 1;
    }
}

/// How a message renders a private declaration's name: Lean's
/// `pp.privateNames` (default `false`, [`Self::UserFacing`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
#[non_exhaustive]
pub(crate) enum PrivateNames {
    /// `pp.privateNames false`: `pd 1 = 2` for a private `pd`.
    #[default]
    UserFacing,
    /// `pp.privateNames true`: the kernel name, `_private.M.0.pd 1 = 2`.
    Raw,
}

impl PrivateNames {
    /// The rendering of `pp.privateNames` given its `set_option` value
    /// (`None` when unset, `Some(None)` for a bare toggle).
    #[must_use]
    pub(crate) fn from_option(value: Option<&Option<String>>) -> Self {
        match value {
            Some(Some(value)) if value == "true" => Self::Raw,
            Some(None) => Self::Raw,
            _ => Self::UserFacing,
        }
    }

    /// `expr` as this mode renders it (RENDERING only, as
    /// [`user_facing_expr`]), in Lean's glyphs ([`lean_glyphs`]): this is the
    /// text of a command's message (`#check`, `#print`), which Lean prints.
    #[must_use]
    pub(crate) fn render(self, expr: &Expr) -> String {
        let rendered = match self {
            Self::UserFacing => user_facing_expr(expr).to_string(),
            Self::Raw => expr.to_string(),
        };
        lean_glyphs(&rendered)
    }
}

/// A rendered term with the ASCII arrow of Clean's term printer (`Nat -> Nat`)
/// spelled as Lean's delaborator prints it (`Nat → Nat`, measured on pinned
/// Lean 4.8.0 and 4.30.0-rc2), outside string literals. The term is the same;
/// only the glyph differs, and a `#check` / `#print` message (and the
/// `#guard_msgs` that compares one) is Lean's text.
#[must_use]
pub(crate) fn lean_glyphs(rendered: &str) -> String {
    let mut out = String::with_capacity(rendered.len());
    let mut in_string = false;
    let mut escaped = false;
    let mut rest = rendered;
    while let Some(ch) = rest.chars().next() {
        if !in_string && rest.starts_with(" -> ") {
            out.push_str(" → ");
            rest = &rest[" -> ".len()..];
            continue;
        }
        if in_string {
            if escaped {
                escaped = false;
            } else if ch == '\\' {
                escaped = true;
            } else if ch == '"' {
                in_string = false;
            }
        } else if ch == '"' {
            in_string = true;
        }
        out.push(ch);
        rest = &rest[ch.len_utf8()..];
    }
    out
}

/// Lean's `isPrivateNameFromImportedModule`: a private name another module
/// minted (`mkPrivateName env (privateToUserName n) != n`). Without a main
/// module every private name is foreign.
#[must_use]
pub(crate) fn is_private_name_from_imported_module(
    main_module: Option<&Name>,
    name: &Name,
) -> bool {
    match (private_to_user_name(name), main_module) {
        (Some(user), Some(module)) => mk_private_name(module, &user) != *name,
        (Some(_), None) => true,
        (None, _) => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn n(s: &str) -> Name {
        Name::from_string(s)
    }

    #[test]
    fn test_lean_glyphs_spell_arrows_as_lean_outside_strings() {
        assert_eq!(lean_glyphs("Nat -> Nat -> Nat"), "Nat → Nat → Nat");
        assert_eq!(
            lean_glyphs("(f : Nat -> Nat) -> Nat"),
            "(f : Nat → Nat) → Nat"
        );
        assert_eq!(
            lean_glyphs("\"a -> b \\\" -> c\" : String"),
            "\"a -> b \\\" -> c\" : String"
        );
        assert_eq!(lean_glyphs("Nat->Nat"), "Nat->Nat");
    }

    #[test]
    fn test_mk_private_name_round_trips_through_the_user_name() {
        let mangled = mk_private_name(&n("Pkg.A"), &n("Foo.helper"));
        assert_eq!(mangled.to_string(), "_private.Pkg.A.0.Foo.helper");
        // `.0.` is a NUMERIC component, so the dotted string parses back.
        assert_eq!(Name::from_string("_private.Pkg.A.0.Foo.helper"), mangled);
        assert!(is_private_name(&mangled));
        assert_eq!(private_to_user_name(&mangled), Some(n("Foo.helper")));
        assert_eq!(user_facing_name(&mangled), n("Foo.helper"));
        assert_eq!(user_facing_name(&n("Foo.helper")), n("Foo.helper"));
        assert!(is_private_prefix(&private_prefix_of(&n("Pkg.A"))));
        assert!(!is_private_prefix(&mangled));
    }

    #[test]
    fn test_mk_private_name_strips_an_existing_private_prefix() {
        let once = mk_private_name(&n("Pkg.A"), &n("helper"));
        assert_eq!(
            mk_private_name(&n("Pkg.B"), &once).to_string(),
            "_private.Pkg.B.0.helper"
        );
        assert_eq!(mk_private_name(&n("Pkg.A"), &once), once);
    }

    #[test]
    fn test_user_name_keeps_numeric_components_after_the_prefix() {
        let mangled = mk_private_name(&n("M"), &Name::anon().str("f").num(3));
        assert_eq!(
            private_to_user_name(&mangled),
            Some(Name::anon().str("f").num(3))
        );
    }

    #[test]
    fn test_user_facing_text_strips_private_prefixes_only() {
        assert_eq!(
            user_facing_text("has type `_private.Pkg.M1.0.pd 1 = 2` (_private.M.0.Foo.x)"),
            "has type `pd 1 = 2` (Foo.x)"
        );
        assert_eq!(
            user_facing_text("_private.«agent-501».«.tmp9».A.0.pt"),
            "pt"
        );
        // Not a private prefix: no `0` after a module, or not a token start.
        for text in [
            "_private.x",
            "_private.0.y",
            "Foo._private.M.0.y",
            "a_private.M.0.y",
        ] {
            assert_eq!(user_facing_text(text), text);
        }
    }

    #[test]
    fn test_plain_names_are_not_private() {
        assert!(!is_private_name(&n("Foo.helper")));
        assert!(!is_private_name(&n("Foo._private.x")));
        assert_eq!(private_to_user_name(&n("helper")), None);
        assert!(!is_private_name_from_imported_module(
            Some(&n("M")),
            &n("helper")
        ));
    }

    #[test]
    fn test_is_private_name_from_imported_module_compares_the_module() {
        let mine = mk_private_name(&n("Pkg.A"), &n("helper"));
        let theirs = mk_private_name(&n("Pkg.B"), &n("helper"));
        assert!(!is_private_name_from_imported_module(
            Some(&n("Pkg.A")),
            &mine
        ));
        assert!(is_private_name_from_imported_module(
            Some(&n("Pkg.A")),
            &theirs
        ));
        assert!(is_private_name_from_imported_module(None, &mine));
    }
}
