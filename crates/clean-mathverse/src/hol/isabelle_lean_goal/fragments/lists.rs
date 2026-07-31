// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! List fragment: `++`, `::` (cons), dot-notation
//! `.map/.filter/.drop/.take/.reverse/.Nodup`, `zip`, `list_all2`, the `[]`
//! literal, and `size` → `.length` (guarded to a list argument, since the `size`
//! class is polymorphic). The Isabelle prefix-with-object-last convention
//! (`map f xs`, `drop n xs`) maps to Lean dot notation with the object as
//! receiver.
//!
//! Faithfulness (checked against Mathlib/Lean `List` defs):
//! * `x # xs` ≡ `x :: xs` (`List.cons`).
//! * `zip xs ys` ≡ `List.zip xs ys` (truncates to the shorter list, as Isabelle).
//! * `distinct xs` ≡ `xs.Nodup` (`List.Nodup`, no repeated element).
//! * `list_all2 R xs ys` ≡ `List.Forall₂ R xs ys` (equal length + pointwise `R`).
//! * `set xs` (`'a list ⇒ 'a set`, the set of the list's elements) ≡
//!   `{x | x ∈ xs}` (`setOf (· ∈ xs)`, membership via `List.Mem` — extensionally
//!   the same element set; no `DecidableEq` needed, unlike `xs.toFinset`).
//! * `sorted_wrt R xs` ≡ `List.Pairwise R xs` — both hold iff `R` relates every
//!   earlier element to every later one (`sorted_wrt R (x#ys) = ((∀y∈set ys. R x
//!   y) ∧ sorted_wrt R ys)` matches `Pairwise R (x::l) ↔ (∀ a ∈ l, R x a) ∧
//!   Pairwise R l`).

use super::super::super::isabelle_pure::IsaTerm;
use super::super::lean_type::is_list_typed;
use super::super::term::{fresh_name, translate_term};
use super::super::types::{prec, BinderKind, LeanTerm, Unsupported};
use super::{binary_infix, method_object_last, prefix_app};

/// Try to render `n` as a list constant.
pub(super) fn try_translate(n: &str, args: &[&IsaTerm]) -> Option<Result<LeanTerm, Unsupported>> {
    let out = match n {
        "List.append" => binary_infix(n, "++", prec::ADD, args),
        // `x # xs` → `x :: xs` (cons binds like `++` for parenthesization).
        "List.list.Cons" => binary_infix(n, "::", prec::ADD, args),
        "List.list.map" => method_object_last(n, "map", 2, args),
        "List.filter" => method_object_last(n, "filter", 2, args),
        "List.drop" => method_object_last(n, "drop", 2, args),
        "List.take" => method_object_last(n, "take", 2, args),
        "List.rev" => method_object_last(n, "reverse", 1, args),
        "List.distinct" => method_object_last(n, "Nodup", 1, args),
        "List.zip" => prefix_app("List.zip", 2, args),
        "List.list.list_all2" => prefix_app("List.Forall₂", 3, args),
        // `set xs` → `{x | x ∈ xs}` (the set of the list's elements).
        "List.list.set" => set_of_list(args),
        // `sorted_wrt R xs` → `List.Pairwise R xs`.
        "List.sorted_wrt" => prefix_app("List.Pairwise", 2, args),
        "List.list.Nil" => nil(args),
        "Nat.size_class.size" => size(args),
        _ => return None,
    };
    Some(out)
}

/// `set xs` → `{x | x ∈ xs}`: the set of the list's elements, as a comprehension
/// over a fresh binder not free in `xs` (capture-safe via [`fresh_name`]).
fn set_of_list(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [xs] = args else {
        return Err(Unsupported::PartialApplication("List.list.set".to_string()));
    };
    let var = fresh_name("x", xs);
    let body = LeanTerm::infix(
        "∈",
        prec::REL,
        LeanTerm::atom(var.clone()),
        translate_term(xs)?,
    );
    Ok(LeanTerm::Binder {
        kind: BinderKind::SetOf,
        var,
        ty: None,
        dom: None,
        body: Box::new(body),
    })
}

/// The empty-list literal `[]`.
fn nil(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    if args.is_empty() {
        Ok(LeanTerm::atom("[]"))
    } else {
        Err(Unsupported::HigherOrder)
    }
}

/// `size xs` → `xs.length`, but **only** when the argument is list-typed. On any
/// other carrier the polymorphic `size` class has no single Lean rendering, so
/// the shape is declined.
fn size(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [xs] = args else {
        return Err(Unsupported::PartialApplication(
            "Nat.size_class.size".to_string(),
        ));
    };
    if !is_list_typed(xs) {
        return Err(Unsupported::NonListSize);
    }
    method_object_last("Nat.size_class.size", "length", 1, args)
}

#[cfg(test)]
mod tests {
    use super::super::super::super::isabelle_pure::{IsaTerm, IsaType};
    use super::super::super::render::render_top;
    use super::*;

    fn tv() -> IsaType {
        IsaType::TVar {
            n: "'a".into(),
            i: 0,
        }
    }
    fn listty() -> IsaType {
        IsaType::Type {
            n: "List.list".into(),
            a: vec![tv()],
        }
    }
    fn lv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: listty(),
        }
    }
    fn append(a: IsaTerm, b: IsaTerm) -> IsaTerm {
        IsaTerm::App {
            f: Box::new(IsaTerm::App {
                f: Box::new(IsaTerm::Const {
                    n: "List.append".into(),
                    t: IsaType::Type {
                        n: "fun".into(),
                        a: vec![
                            listty(),
                            IsaType::Type {
                                n: "fun".into(),
                                a: vec![listty(), listty()],
                            },
                        ],
                    },
                }),
                a: Box::new(a),
            }),
            a: Box::new(b),
        }
    }

    #[test]
    fn append_is_infix() {
        let out = try_translate("List.append", &[&lv("xs"), &lv("ys")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "xs ++ ys");
    }

    #[test]
    fn size_of_list_is_length() {
        let ap = append(lv("xs"), lv("ys"));
        let out = try_translate("Nat.size_class.size", &[&ap])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "(xs ++ ys).length");
    }

    #[test]
    fn size_of_nonlist_declined() {
        let n = IsaTerm::Var {
            n: "x".into(),
            i: 0,
            t: tv(),
        };
        assert!(matches!(
            try_translate("Nat.size_class.size", &[&n]),
            Some(Err(Unsupported::NonListSize))
        ));
    }

    #[test]
    fn map_object_last() {
        let f = IsaTerm::Var {
            n: "f".into(),
            i: 0,
            t: tv(),
        };
        let out = try_translate("List.list.map", &[&f, &lv("xs")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "xs.map f");
    }

    #[test]
    fn cons_is_infix() {
        let x = IsaTerm::Var {
            n: "x".into(),
            i: 0,
            t: tv(),
        };
        // x # (ys ++ zs) fully parenthesizes the looser append operand.
        let app = append(lv("ys"), lv("zs"));
        let out = try_translate("List.list.Cons", &[&x, &app])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "x :: (ys ++ zs)");
    }

    #[test]
    fn distinct_is_nodup_method() {
        let out = try_translate("List.distinct", &[&lv("xs")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "xs.Nodup");
    }

    #[test]
    fn zip_and_list_all2_are_prefix() {
        let out = try_translate("List.zip", &[&lv("xs"), &lv("ys")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "List.zip xs ys");
        let r = IsaTerm::Var {
            n: "R".into(),
            i: 0,
            t: tv(),
        };
        let out = try_translate("List.list.list_all2", &[&r, &lv("xs"), &lv("ys")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "List.Forall₂ R xs ys");
    }

    #[test]
    fn set_of_list_is_comprehension() {
        // `set xs` → `{x | x ∈ xs}`; the fresh binder avoids the list name.
        let out = try_translate("List.list.set", &[&lv("xs")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "{x | x ∈ xs}");
        // A list literally named `x` forces the binder to freshen to `x_1`.
        let out = try_translate("List.list.set", &[&lv("x")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "{x_1 | x_1 ∈ x}");
    }

    #[test]
    fn sorted_wrt_is_pairwise() {
        let r = IsaTerm::Var {
            n: "R".into(),
            i: 0,
            t: tv(),
        };
        let out = try_translate("List.sorted_wrt", &[&r, &lv("xs")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "List.Pairwise R xs");
    }
}
