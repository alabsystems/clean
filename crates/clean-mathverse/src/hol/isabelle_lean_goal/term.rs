// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The object-term translator: peel an Isabelle application spine to its head +
//! argument list, then dispatch the head to the fragment pattern library. Any
//! shape no fragment claims — or any bound/λ subterm — becomes a first-class
//! [`Unsupported`] verdict; nothing is guessed.

use std::collections::HashSet;

use super::super::isabelle_pure::{IsaTerm, IsaType};
use super::fragments;
use super::types::{LeanTerm, Unsupported};

/// Peel a left-nested application `((h a₁) a₂) … aₙ` into its head `h` and the
/// argument list `[a₁, …, aₙ]` (in source order).
#[must_use]
pub fn peel_spine(t: &IsaTerm) -> (&IsaTerm, Vec<&IsaTerm>) {
    let mut args: Vec<&IsaTerm> = Vec::new();
    let mut head = t;
    while let IsaTerm::App { f, a } = head {
        args.push(a);
        head = f;
    }
    args.reverse();
    (head, args)
}

/// Translate an object-level (`bool`-valued) Isabelle term to a [`LeanTerm`].
///
/// # Errors
/// [`Unsupported`] for any constant outside the pattern library, a higher-order
/// subterm, or a fragment guard that declines (polymorphic order/lattice, etc.).
pub fn translate_term(t: &IsaTerm) -> Result<LeanTerm, Unsupported> {
    let (head, args) = peel_spine(t);
    match head {
        IsaTerm::Const { n, t } => match fragments::dispatch(n, t, &args) {
            Some(res) => res,
            None => Err(Unsupported::UnknownConst(n.clone())),
        },
        IsaTerm::Var { n, .. } | IsaTerm::Free { n, .. } => {
            if args.is_empty() {
                Ok(LeanTerm::atom(clean_ident(n)))
            } else {
                // A higher-order variable application `?P ?x …` renders as a
                // faithful prefix application.
                let rendered: Result<Vec<LeanTerm>, Unsupported> =
                    args.iter().map(|a| translate_term(a)).collect();
                Ok(LeanTerm::App {
                    head: clean_ident(n),
                    args: rendered?,
                })
            }
        }
        // A bound variable outside a supported binder, or a bare λ, is a
        // higher-order shape the statement library does not render.
        IsaTerm::Bound { .. } | IsaTerm::Abs { .. } => Err(Unsupported::HigherOrder),
        // Unreachable: `peel_spine` strips every `App` layer.
        IsaTerm::App { .. } => Err(Unsupported::HigherOrder),
    }
}

/// Strip a leading schematic `?` from an Isabelle variable name so the binder
/// reads naturally (`?xs` → `xs`). Isabelle `Var` names in the export carry no
/// `?`, but a defensive strip keeps hand-authored fixtures honest.
#[must_use]
pub fn clean_ident(n: &str) -> String {
    n.strip_prefix('?').unwrap_or(n).to_string()
}

/// Open an Isabelle `Abs` binder for rendering as a named Lean binder.
///
/// This is the object-term analogue of the translate lane's `IsaTerm::Abs`
/// opening (`embed_term`): pick a **capture-safe** Lean name for the bound
/// variable (from the Isabelle-suggested `n`, falling back / freshening so it
/// avoids every name already free in `body`), then instantiate the innermost de
/// Bruijn variable (`Bound 0` at the top of `body`) with a matching closed
/// [`IsaTerm::Free`] and decrement the outer indices. Returns the chosen name,
/// the domain type (verbatim, for an optional concrete annotation), and the
/// opened body — which no longer references the opened binder as a loose `Bound`.
///
/// Capture-safety is exact: a nested binder that would shadow an outer one is
/// renamed, because the outer binder has *already* been substituted to a `Free`
/// in `body` and so appears in the avoided free-name set (`∀x. ∀x. P x x` →
/// `∀ x, ∀ x_1, P x x_1`).
#[must_use]
pub(super) fn open_abs(n: &str, t: &IsaType, body: &IsaTerm) -> (String, IsaType, IsaTerm) {
    let var = fresh_name(n, body);
    let repl = IsaTerm::Free {
        n: var.clone(),
        t: t.clone(),
    };
    let opened = instantiate_bound(body, &repl, 0);
    (var, t.clone(), opened)
}

/// A capture-safe Lean binder name derived from the Isabelle-suggested `n`,
/// avoiding every name already free (`Free`/`Var`) in `body`. Freshens by
/// appending `_1`, `_2`, … on a clash.
#[must_use]
pub(super) fn fresh_name(n: &str, body: &IsaTerm) -> String {
    let mut used: HashSet<String> = HashSet::new();
    free_names(body, &mut used);
    let base = sanitize_ident(n);
    if !used.contains(&base) {
        return base;
    }
    let mut k = 1usize;
    loop {
        let cand = format!("{base}_{k}");
        if !used.contains(&cand) {
            return cand;
        }
        k += 1;
    }
}

/// Collect the `Free`/`Var` names (via [`clean_ident`]) appearing anywhere in
/// `term` — the set a freshly-opened binder name must avoid to stay capture-safe.
/// `Bound` variables carry no name and are skipped; `Abs` bodies are still
/// walked (an inner binder's free vars still constrain the outer fresh name).
fn free_names(term: &IsaTerm, out: &mut HashSet<String>) {
    match term {
        IsaTerm::Free { n, .. } | IsaTerm::Var { n, .. } => {
            out.insert(clean_ident(n));
        }
        IsaTerm::App { f, a } => {
            free_names(f, out);
            free_names(a, out);
        }
        IsaTerm::Abs { b, .. } => free_names(b, out),
        IsaTerm::Const { .. } | IsaTerm::Bound { .. } => {}
    }
}

/// Substitute the binder being opened — `Bound depth` — with the closed `repl`,
/// and decrement every strictly-outer `Bound i` (`i > depth`) by one; inner
/// binders (`i < depth`) are left untouched. `depth` increases by one under each
/// `Abs`. Because `repl` is closed (a `Free`), it needs no shifting under inner
/// binders.
fn instantiate_bound(term: &IsaTerm, repl: &IsaTerm, depth: i64) -> IsaTerm {
    match term {
        IsaTerm::Bound { i } => {
            if *i == depth {
                repl.clone()
            } else if *i > depth {
                IsaTerm::Bound { i: i - 1 }
            } else {
                term.clone()
            }
        }
        IsaTerm::App { f, a } => IsaTerm::App {
            f: Box::new(instantiate_bound(f, repl, depth)),
            a: Box::new(instantiate_bound(a, repl, depth)),
        },
        IsaTerm::Abs { n, t, b } => IsaTerm::Abs {
            n: n.clone(),
            t: t.clone(),
            b: Box::new(instantiate_bound(b, repl, depth + 1)),
        },
        IsaTerm::Const { .. } | IsaTerm::Free { .. } | IsaTerm::Var { .. } => term.clone(),
    }
}

/// Coerce an Isabelle-suggested binder name to a plausible Lean identifier,
/// falling back to `x` for an empty or non-identifier name (a keyword collision
/// is left to surface as a *loud* Lean parse error — never a silent mis-binding).
fn sanitize_ident(n: &str) -> String {
    let n = clean_ident(n);
    let mut chars = n.chars();
    let ok = matches!(chars.next(), Some(c) if c.is_ascii_alphabetic() || c == '_')
        && n.chars()
            .all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '\'');
    if ok {
        n
    } else {
        "x".to_string()
    }
}

#[cfg(test)]
mod tests {
    use super::super::super::isabelle_pure::{IsaTerm, IsaType};
    use super::*;

    fn nat() -> IsaType {
        IsaType::Type {
            n: "Nat.nat".into(),
            a: vec![],
        }
    }
    fn v(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: nat(),
        }
    }

    #[test]
    fn peels_curried_spine() {
        // f a b
        let t = IsaTerm::App {
            f: Box::new(IsaTerm::App {
                f: Box::new(IsaTerm::Const {
                    n: "F".into(),
                    t: nat(),
                }),
                a: Box::new(v("a")),
            }),
            a: Box::new(v("b")),
        };
        let (head, args) = peel_spine(&t);
        assert!(matches!(head, IsaTerm::Const { n, .. } if n == "F"));
        assert_eq!(args.len(), 2);
    }

    #[test]
    fn bare_var_is_atom() {
        assert_eq!(translate_term(&v("xs")).unwrap(), LeanTerm::atom("xs"));
    }

    #[test]
    fn unknown_const_is_unsupported() {
        let t = IsaTerm::Const {
            n: "Frobnicate.widget".into(),
            t: nat(),
        };
        assert!(matches!(
            translate_term(&t),
            Err(Unsupported::UnknownConst(_))
        ));
    }
}
