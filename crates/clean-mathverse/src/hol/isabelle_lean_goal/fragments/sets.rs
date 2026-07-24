// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Set fragment: the `Set`-lattice operators `sup`/`inf` (`∪`/`∩`, guarded to a
//! `Set` operand), plus the monomorphic set predicates/operators that render
//! faithfully with no guard because the Isabelle constant is itself set-specific:
//! `Set.member` (`∈`), `Set.image` (`f '' A`), `Set.insert` (`insert a A`),
//! `Finite_Set.finite` (`A.Finite`), `Fun.inj_on` (`Set.InjOn`), `Fun.bij_betw`
//! (`Set.BijOn`).
//!
//! Faithfulness (checked against Mathlib defs):
//! * `Set.member x A` ≡ `x ∈ A` (`Membership.mem`).
//! * `Set.image f A = {y. ∃x∈A. y = f x}` ≡ `Set.image f A` (`f '' A`).
//! * `Set.insert a A = {a} ∪ A` ≡ `insert a A` (`Set.instInsert`).
//! * `Finite_Set.finite A` ≡ `Set.Finite A` (`A.Finite`).
//! * `Fun.inj_on f A` ≡ `Set.InjOn f A` (`∀x∈A,∀y∈A, f x = f y → x = y`).
//! * `Fun.bij_betw f A B` ≡ `Set.BijOn f A B` (`MapsTo ∧ InjOn ∧ SurjOn`).
//!
//! On any non-`Set` carrier `sup`/`inf` are generic lattice `⊔`/`⊓`, whose Lean
//! class instance is not statement-determined, so those shapes are declined
//! ([`Unsupported::PolymorphicLattice`]) rather than guessed.

use super::super::super::isabelle_pure::IsaTerm;
use super::super::lean_type::is_set_typed;
use super::super::term::translate_term;
use super::super::types::{prec, LeanTerm, Unsupported};
use super::{binary_infix, method_object_last, prefix_app};

/// Try to render `n` as a set operator / predicate.
pub(super) fn try_translate(n: &str, args: &[&IsaTerm]) -> Option<Result<LeanTerm, Unsupported>> {
    let out = match n {
        "Lattices.sup_class.sup" => set_binop(n, "∪", args),
        "Lattices.inf_class.inf" => set_binop(n, "∩", args),
        // `Set.member x A` → `x ∈ A` (monomorphic set membership).
        "Set.member" => member(args),
        // `Set.image f A` → `Set.image f A` (surface `f '' A`).
        "Set.image" => prefix_app("Set.image", 2, args),
        // `Set.insert a A` → `insert a A`.
        "Set.insert" => prefix_app("insert", 2, args),
        // `finite A` → `A.Finite` (`Set.Finite A`).
        "Finite_Set.finite" => method_object_last("Finite_Set.finite", "Finite", 1, args),
        // `inj_on f A` → `Set.InjOn f A`.
        "Fun.inj_on" => prefix_app("Set.InjOn", 2, args),
        // `bij_betw f A B` → `Set.BijOn f A B`.
        "Fun.bij_betw" => prefix_app("Set.BijOn", 3, args),
        _ => return None,
    };
    Some(out)
}

/// A lattice binary operator guarded to a `Set`-typed operand.
fn set_binop(n: &str, op: &'static str, args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [l, _] = args else {
        return Err(Unsupported::PartialApplication(n.to_string()));
    };
    if !is_set_typed(l) {
        return Err(Unsupported::PolymorphicLattice(n.to_string()));
    }
    binary_infix(n, op, prec::LATTICE, args)
}

/// `Set.member x A` → `x ∈ A`. The Isabelle constant is monomorphic set
/// membership (`'a ⇒ 'a set ⇒ bool`), so no carrier guard is needed.
fn member(args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [x, a] = args else {
        return Err(Unsupported::PartialApplication("Set.member".to_string()));
    };
    Ok(LeanTerm::infix(
        "∈",
        prec::REL,
        translate_term(x)?,
        translate_term(a)?,
    ))
}

#[cfg(test)]
mod tests {
    use super::super::super::super::isabelle_pure::{IsaTerm, IsaType};
    use super::super::super::render::render_top;
    use super::*;

    fn setty() -> IsaType {
        IsaType::Type {
            n: "Set.set".into(),
            a: vec![IsaType::TVar {
                n: "'a".into(),
                i: 0,
            }],
        }
    }
    fn tv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: IsaType::TVar {
                n: "'a".into(),
                i: 0,
            },
        }
    }
    fn sv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: setty(),
        }
    }
    fn fv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: IsaType::Type {
                n: "fun".into(),
                a: vec![
                    IsaType::TVar {
                        n: "'a".into(),
                        i: 0,
                    },
                    IsaType::TVar {
                        n: "'b".into(),
                        i: 0,
                    },
                ],
            },
        }
    }

    #[test]
    fn set_sup_is_union() {
        let out = try_translate("Lattices.sup_class.sup", &[&sv("A"), &sv("B")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "A ∪ B");
    }

    #[test]
    fn nonset_lattice_declined() {
        let x = tv("x");
        assert!(matches!(
            try_translate("Lattices.inf_class.inf", &[&x, &x]),
            Some(Err(Unsupported::PolymorphicLattice(_)))
        ));
    }

    #[test]
    fn member_is_in() {
        let out = try_translate("Set.member", &[&tv("x"), &sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "x ∈ A");
    }

    #[test]
    fn member_of_insert() {
        let insert = IsaTerm::App {
            f: Box::new(IsaTerm::App {
                f: Box::new(IsaTerm::Const {
                    n: "Set.insert".into(),
                    t: setty(),
                }),
                a: Box::new(tv("a")),
            }),
            a: Box::new(sv("B")),
        };
        let out = try_translate("Set.member", &[&tv("a"), &insert])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "a ∈ insert a B");
    }

    #[test]
    fn image_is_prefix() {
        let out = try_translate("Set.image", &[&fv("f"), &sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "Set.image f A");
    }

    #[test]
    fn finite_is_method() {
        let out = try_translate("Finite_Set.finite", &[&sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "A.Finite");
    }

    #[test]
    fn inj_on_and_bij_betw() {
        let out = try_translate("Fun.inj_on", &[&fv("f"), &sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "Set.InjOn f A");
        let out = try_translate("Fun.bij_betw", &[&fv("f"), &sv("A"), &sv("B")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "Set.BijOn f A B");
    }
}
