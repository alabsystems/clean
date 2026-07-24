// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! HOL-to-clean type and term translation.
//!
//! Maps HOL's simple type theory into clean's dependent type theory:
//!
//! | HOL                | clean              |
//! |--------------------|--------------------|
//! | `bool`             | `Prop`             |
//! | `ind`              | `Nat` (infinite)   |
//! | `fun A B`          | `A -> B`           |
//! | `'a` (tyvar)       | universe variable  |
//! | `Var(x, ty)`       | `FVar(x)`          |
//! | `Const(c, ty)`     | `Const(c, [ty])`   |
//! | `App(f, a)`        | `App(f, a)`        |
//! | `Abs(x, ty, body)` | `Lambda(x, ty, b)` |
//!
//! The translation is compositional and preserves simple typing. Since HOL
//! lacks dependent types, the image lives in the non-dependent fragment of
//! clean's type theory.
//!
//! Reference: Obua et al., "Importing HOL into Isabelle/HOL" (2006);
//! Kaliszyk & Krauss, "Scalable LCF-style proof translation" (2013).

use super::types::{HolTerm, HolType};
use super::HolError;

// ---------------------------------------------------------------------------
// Type translation
// ---------------------------------------------------------------------------

/// Translate a HOL type to a clean type expression string.
///
/// The result is a human-readable clean type expression. For actual kernel
/// `Expr` construction, downstream code would parse or build these from the
/// string representation.
pub fn translate_type(ty: &HolType) -> Result<String, HolError> {
    match ty {
        HolType::TyVar(name) => Ok(name.clone()),
        HolType::TyOp(name, args) => match (name.as_str(), args.as_slice()) {
            ("bool", []) => Ok("Prop".to_owned()),
            ("ind", []) => Ok("Nat".to_owned()),
            ("fun", [dom, cod]) => {
                let dom_str = translate_type(dom)?;
                let cod_str = translate_type(cod)?;
                // Parenthesize domain if it's a function type (right-associative).
                let dom_str = if dom.is_fun() {
                    format!("({dom_str})")
                } else {
                    dom_str
                };
                Ok(format!("{dom_str} -> {cod_str}"))
            }
            ("fun", _) => Err(HolError::TranslationError {
                message: format!("`fun` expects 2 args, got {}", args.len()),
            }),
            // User-defined type operators.
            (op, []) => Ok(op.to_owned()),
            (op, _) => {
                let arg_strs: Result<Vec<_>, _> = args.iter().map(translate_type).collect();
                let arg_strs = arg_strs?;
                Ok(format!("{op} {}", arg_strs.join(" ")))
            }
        },
    }
}

// ---------------------------------------------------------------------------
// Term translation
// ---------------------------------------------------------------------------

/// Translate a HOL term to a clean term expression string.
///
/// Produces a human-readable clean expression. Well-typed HOL terms always
/// produce well-typed clean terms under the type translation above.
pub fn translate_term(tm: &HolTerm) -> Result<String, HolError> {
    match tm {
        HolTerm::Var(name, _) => Ok(name.clone()),
        HolTerm::Const(name, _) => {
            // Map well-known HOL constants to clean equivalents.
            let lean_name = match name.as_str() {
                "T" => "True",
                "F" => "False",
                "=" => "Eq",
                "==>" => "implies",
                "/\\" | "∧" => "And",
                "\\/" | "∨" => "Or",
                "~" | "¬" => "Not",
                "!" | "∀" => "forall",
                "?" | "∃" => "Exists",
                "@" => "Classical.choice",
                other => other,
            };
            Ok(lean_name.to_owned())
        }
        HolTerm::App(f, a) => {
            let f_str = translate_term(f)?;
            let a_str = translate_term(a)?;
            // Parenthesize argument if it's an application (left-associative).
            let a_str = if matches!(a.as_ref(), HolTerm::App(..)) {
                format!("({a_str})")
            } else {
                a_str
            };
            Ok(format!("{f_str} {a_str}"))
        }
        HolTerm::Abs(var, ty, body) => {
            let ty_str = translate_type(ty)?;
            let body_str = translate_term(body)?;
            Ok(format!("fun ({var} : {ty_str}) => {body_str}"))
        }
    }
}

/// Translate a HOL theorem to a clean statement string.
///
/// Hypotheses become antecedents of an implication chain.
pub fn translate_theorem(thm: &super::types::HolThm) -> Result<String, HolError> {
    let concl_str = translate_term(&thm.concl)?;

    if thm.hyps.is_empty() {
        return Ok(concl_str);
    }

    let mut hyp_strs = Vec::with_capacity(thm.hyps.len());
    for h in &thm.hyps {
        hyp_strs.push(translate_term(h)?);
    }

    // Chain: h1 -> h2 -> ... -> concl
    let mut result = concl_str;
    for h in hyp_strs.into_iter().rev() {
        result = format!("{h} -> {result}");
    }
    Ok(result)
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::progverif::hol::types::{HolThm, HolType};

    #[test]
    fn test_translate_type_bool() {
        assert_eq!(translate_type(&HolType::bool()).unwrap(), "Prop");
    }

    #[test]
    fn test_translate_type_ind() {
        assert_eq!(translate_type(&HolType::ind()).unwrap(), "Nat");
    }

    #[test]
    fn test_translate_type_tyvar() {
        let ty = HolType::TyVar("'a".to_owned());
        assert_eq!(translate_type(&ty).unwrap(), "'a");
    }

    #[test]
    fn test_translate_type_fun() {
        let ty = HolType::fun(HolType::bool(), HolType::bool());
        assert_eq!(translate_type(&ty).unwrap(), "Prop -> Prop");
    }

    #[test]
    fn test_translate_type_nested_fun() {
        // (bool -> bool) -> bool
        let inner = HolType::fun(HolType::bool(), HolType::bool());
        let outer = HolType::fun(inner, HolType::bool());
        assert_eq!(translate_type(&outer).unwrap(), "(Prop -> Prop) -> Prop");
    }

    #[test]
    fn test_translate_type_user_defined() {
        let ty = HolType::TyOp("list".to_owned(), vec![HolType::TyVar("'a".to_owned())]);
        assert_eq!(translate_type(&ty).unwrap(), "list 'a");
    }

    #[test]
    fn test_translate_type_fun_bad_arity() {
        let ty = HolType::TyOp("fun".to_owned(), vec![HolType::bool()]);
        assert!(translate_type(&ty).is_err());
    }

    #[test]
    fn test_translate_term_var() {
        let tm = HolTerm::Var("x".to_owned(), HolType::bool());
        assert_eq!(translate_term(&tm).unwrap(), "x");
    }

    #[test]
    fn test_translate_term_const_truth() {
        let tm = HolTerm::Const("T".to_owned(), HolType::bool());
        assert_eq!(translate_term(&tm).unwrap(), "True");
    }

    #[test]
    fn test_translate_term_const_false() {
        let tm = HolTerm::Const("F".to_owned(), HolType::bool());
        assert_eq!(translate_term(&tm).unwrap(), "False");
    }

    #[test]
    fn test_translate_term_app() {
        let f = HolTerm::Const(
            "~".to_owned(),
            HolType::fun(HolType::bool(), HolType::bool()),
        );
        let a = HolTerm::Const("T".to_owned(), HolType::bool());
        let tm = HolTerm::App(Box::new(f), Box::new(a));
        assert_eq!(translate_term(&tm).unwrap(), "Not True");
    }

    #[test]
    fn test_translate_term_abs() {
        let body = HolTerm::Var("x".to_owned(), HolType::bool());
        let tm = HolTerm::Abs("x".to_owned(), HolType::bool(), Box::new(body));
        assert_eq!(translate_term(&tm).unwrap(), "fun (x : Prop) => x");
    }

    #[test]
    fn test_translate_theorem_no_hyps() {
        let thm = HolThm {
            hyps: vec![],
            concl: HolTerm::Const("T".to_owned(), HolType::bool()),
        };
        assert_eq!(translate_theorem(&thm).unwrap(), "True");
    }

    #[test]
    fn test_translate_theorem_with_hyps() {
        let p = HolTerm::Var("P".to_owned(), HolType::bool());
        let q = HolTerm::Var("Q".to_owned(), HolType::bool());
        let thm = HolThm {
            hyps: vec![p.clone()],
            concl: q,
        };
        assert_eq!(translate_theorem(&thm).unwrap(), "P -> Q");
    }

    #[test]
    fn test_translate_theorem_multiple_hyps() {
        let a = HolTerm::Var("A".to_owned(), HolType::bool());
        let b = HolTerm::Var("B".to_owned(), HolType::bool());
        let c = HolTerm::Var("C".to_owned(), HolType::bool());
        let thm = HolThm {
            hyps: vec![a, b],
            concl: c,
        };
        assert_eq!(translate_theorem(&thm).unwrap(), "A -> B -> C");
    }

    #[test]
    fn test_translate_const_mapping() {
        for (hol, lean) in &[
            ("=", "Eq"),
            ("==>", "implies"),
            ("/\\", "And"),
            ("\\/", "Or"),
            ("~", "Not"),
            ("!", "forall"),
            ("?", "Exists"),
            ("@", "Classical.choice"),
        ] {
            let tm = HolTerm::Const(hol.to_string(), HolType::bool());
            assert_eq!(translate_term(&tm).unwrap(), *lean);
        }
    }
}
