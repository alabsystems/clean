// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic fragment: the additive-group / ring operators (`+ - *`), unary
//! minus, divisibility, the numeric identities (`0`, `1`), `Suc`, and the
//! `int → nat` cast. The `+ - *` / unary-`-` operators are class-generic in
//! Isabelle but render to the same Lean surface on every carrier, so no type
//! guard is needed — `a + b`, `-a` are faithful whether the carrier is `ℕ` or a
//! bare `α` (if the carrier lacks the instance the *elaborator* rejects it
//! loudly; the translation is never silently wrong).
//!
//! Faithfulness (checked against Mathlib/Lean defs):
//! * `Rings.dvd_class.dvd a b` ≡ `a ∣ b` (`Dvd.dvd`, `∃c. b = a*c`).
//! * `Groups.uminus_class.uminus a` ≡ `-a` (`Neg.neg`).
//! * `Int.nat i` ≡ `i.toNat` (`Int.toNat`, `= 0` on negatives — matching
//!   Isabelle's `nat` of a negative).

use super::super::super::isabelle_pure::IsaTerm;
use super::super::term::translate_term;
use super::super::types::{prec, LeanTerm, Unsupported};
use super::{binary_infix, method_object_last};

/// Try to render `n` as an arithmetic constant.
pub(super) fn try_translate(n: &str, args: &[&IsaTerm]) -> Option<Result<LeanTerm, Unsupported>> {
    let out = match n {
        "Groups.plus_class.plus" => binary_infix(n, "+", prec::ADD, args),
        "Groups.minus_class.minus" => binary_infix(n, "-", prec::ADD, args),
        "Groups.times_class.times" => binary_infix(n, "*", prec::MUL, args),
        // Divisibility: `Dvd.dvd`, faithful on any carrier with a `Dvd` instance.
        "Rings.dvd_class.dvd" | "Rings.dvd.dvd" => binary_infix(n, "∣", prec::REL, args),
        "Groups.zero_class.zero" => nullary("0", args),
        "Groups.one_class.one" => nullary("1", args),
        "Groups.uminus_class.uminus" => uminus(args),
        "Nat.Suc" => suc(args),
        // `nat i` (int → nat cast) → `i.toNat`.
        "Int.nat" => method_object_last("Int.nat", "toNat", 1, args),
        _ => return None,
    };
    Some(out)
}

/// `Groups.uminus_class.uminus a` → `-a`.
fn uminus(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [a] = args else {
        return Err(Unsupported::PartialApplication(
            "Groups.uminus_class.uminus".to_string(),
        ));
    };
    Ok(LeanTerm::Prefix {
        op: "-",
        arg: Box::new(translate_term(a)?),
    })
}

/// A nullary literal constant (`0`, `1`). Any application is a shape we do not
/// model.
fn nullary(lit: &'static str, args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    if args.is_empty() {
        Ok(LeanTerm::atom(lit))
    } else {
        Err(Unsupported::HigherOrder)
    }
}

/// `Nat.Suc n` → `Nat.succ n`.
fn suc(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [n] = args else {
        return Err(Unsupported::PartialApplication("Nat.Suc".to_string()));
    };
    Ok(LeanTerm::App {
        head: "Nat.succ".to_string(),
        args: vec![translate_term(n)?],
    })
}

#[cfg(test)]
mod tests {
    use super::super::super::super::isabelle_pure::{IsaTerm, IsaType};
    use super::super::super::render::render_top;
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
    fn plus_times_precedence() {
        // (m + n) * k
        let mn = IsaTerm::App {
            f: Box::new(IsaTerm::App {
                f: Box::new(IsaTerm::Const {
                    n: "Groups.plus_class.plus".into(),
                    t: nat(),
                }),
                a: Box::new(v("m")),
            }),
            a: Box::new(v("n")),
        };
        let out = try_translate("Groups.times_class.times", &[&mn, &v("k")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "(m + n) * k");
    }

    #[test]
    fn zero_is_atom() {
        let out = try_translate("Groups.zero_class.zero", &[])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "0");
    }

    #[test]
    fn dvd_is_infix() {
        let out = try_translate("Rings.dvd_class.dvd", &[&v("a"), &v("b")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "a ∣ b");
        // the alternate spelling routes identically
        let out = try_translate("Rings.dvd.dvd", &[&v("a"), &v("b")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "a ∣ b");
    }

    #[test]
    fn uminus_is_prefix() {
        let out = try_translate("Groups.uminus_class.uminus", &[&v("a")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "- a");
    }

    #[test]
    fn int_nat_is_tonat_method() {
        let iv = IsaTerm::Var {
            n: "i".into(),
            i: 0,
            t: IsaType::Type {
                n: "Int.int".into(),
                a: vec![],
            },
        };
        let out = try_translate("Int.nat", &[&iv]).unwrap().unwrap();
        assert_eq!(render_top(&out), "i.toNat");
    }
}
