// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The object-term translator: peel an Isabelle application spine to its head +
//! argument list, then dispatch the head to the fragment pattern library. Any
//! shape no fragment claims — or any bound/λ subterm — becomes a first-class
//! [`Unsupported`] verdict; nothing is guessed.

use super::super::isabelle_pure::IsaTerm;
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
        IsaTerm::Const { n, .. } => match fragments::dispatch(n, &args) {
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
