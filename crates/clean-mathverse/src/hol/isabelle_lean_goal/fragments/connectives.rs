// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Connective fragment: HOL propositional/equality constants, the truth values
//! `True`/`False`, function composition, and the identity function. `HOL.eq`
//! covers both object equality and the Bool/Prop-eq shape the batch renders
//! literally as `=`.
//!
//! Faithfulness: `HOL.True`/`HOL.False` ≡ Lean `True`/`False`; `Fun.id` ≡ `id`
//! (`fun a => a`, polymorphic in both systems — faithful applied or nullary).

use super::super::super::isabelle_pure::IsaTerm;
use super::super::term::translate_term;
use super::super::types::{prec, LeanTerm, Unsupported};
use super::binary_infix;

/// Try to render `n` as a connective / composition / truth value.
pub(super) fn try_translate(n: &str, args: &[&IsaTerm]) -> Option<Result<LeanTerm, Unsupported>> {
    let out = match n {
        "HOL.eq" => binary_infix(n, "=", prec::EQ, args),
        "HOL.disj" => binary_infix(n, "∨", prec::DISJ, args),
        "HOL.conj" => binary_infix(n, "∧", prec::CONJ, args),
        "HOL.implies" => binary_infix(n, "→", prec::IMPLIES, args),
        "Fun.comp" => binary_infix(n, "∘", prec::COMP, args),
        "HOL.Not" => not_prefix(args),
        "HOL.True" => truth("True", args),
        "HOL.False" => truth("False", args),
        // `Fun.id` is polymorphic identity: `id`, or `id x` when applied.
        "Fun.id" => id(args),
        _ => return None,
    };
    Some(out)
}

/// A nullary truth value (`True`/`False`). Any application is a shape we do not
/// model.
fn truth(lit: &'static str, args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    if args.is_empty() {
        Ok(LeanTerm::atom(lit))
    } else {
        Err(Unsupported::HigherOrder)
    }
}

/// `Fun.id` → `id` (nullary) / `id x …` (applied). `id` is generic in Lean, so
/// this is faithful at any arity.
fn id(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let rendered: Result<Vec<LeanTerm>, Unsupported> =
        args.iter().map(|a| translate_term(a)).collect();
    Ok(LeanTerm::App {
        head: "id".to_string(),
        args: rendered?,
    })
}

/// `HOL.Not p` → `¬ p`.
fn not_prefix(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [p] = args else {
        return Err(Unsupported::PartialApplication("HOL.Not".to_string()));
    };
    Ok(LeanTerm::Prefix {
        op: "¬",
        arg: Box::new(translate_term(p)?),
    })
}

#[cfg(test)]
mod tests {
    use super::super::super::super::isabelle_pure::{IsaTerm, IsaType};
    use super::super::super::render::render_top;
    use super::*;

    fn boolty() -> IsaType {
        IsaType::Type {
            n: "HOL.bool".into(),
            a: vec![],
        }
    }
    fn v(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: boolty(),
        }
    }

    #[test]
    fn eq_is_infix() {
        let out = try_translate("HOL.eq", &[&v("a"), &v("b")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "a = b");
    }

    #[test]
    fn not_is_prefix() {
        let out = try_translate("HOL.Not", &[&v("p")]).unwrap().unwrap();
        assert_eq!(render_top(&out), "¬ p");
    }

    #[test]
    fn unknown_returns_none() {
        assert!(try_translate("Nope.nope", &[]).is_none());
    }

    #[test]
    fn truth_values_and_id() {
        assert_eq!(
            render_top(&try_translate("HOL.True", &[]).unwrap().unwrap()),
            "True"
        );
        assert_eq!(
            render_top(&try_translate("HOL.False", &[]).unwrap().unwrap()),
            "False"
        );
        // nullary id
        assert_eq!(
            render_top(&try_translate("Fun.id", &[]).unwrap().unwrap()),
            "id"
        );
        // applied id
        assert_eq!(
            render_top(&try_translate("Fun.id", &[&v("x")]).unwrap().unwrap()),
            "id x"
        );
    }
}
