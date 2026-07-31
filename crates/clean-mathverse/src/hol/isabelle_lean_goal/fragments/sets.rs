// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Set fragment: the `Set`-lattice operators `sup`/`inf` (`∪`/`∩`, guarded to a
//! `Set` operand), the nullary lattice bounds `bot`/`top` (`∅`/`Set.univ`,
//! guarded on the head-constant type), the complete-lattice `Sup`/`Inf`
//! (`sSup`/`sInf`, guarded to a set-of-sets operand), plus the monomorphic set
//! predicates/operators that render faithfully with no guard because the Isabelle
//! constant is itself set-specific: `Set.member` (`∈`), `Set.image` (`f '' A`),
//! `Set.insert` (`insert a A`), `Finite_Set.finite` (`A.Finite`),
//! `Finite_Set.card` (`A.ncard`), `Fun.inj_on` (`Set.InjOn`), `Fun.bij_betw`
//! (`Set.BijOn`).
//!
//! Faithfulness (checked against Mathlib defs):
//! * `Set.member x A` ≡ `x ∈ A` (`Membership.mem`).
//! * `Set.image f A = {y. ∃x∈A. y = f x}` ≡ `Set.image f A` (`f '' A`).
//! * `Set.insert a A = {a} ∪ A` ≡ `insert a A` (`Set.instInsert`).
//! * `Finite_Set.finite A` ≡ `Set.Finite A` (`A.Finite`).
//! * `Finite_Set.card A` ≡ `Set.ncard A` (`A.ncard`) — both are the ℕ-valued
//!   cardinality that is the element count on a finite set and junk-`0` on an
//!   infinite one (Mathlib `Set.ncard s = s.toFinite.toFinset.card` via
//!   `Nat.card`, matching Isabelle `card A = 0` for infinite `A`).
//! * `bot :: 'a set = {}` ≡ `(∅ : Set α)` (`Set` `OrderBot`, `⊥ = ∅`).
//! * `top :: 'a set = UNIV` ≡ `Set.univ` (`Set` `OrderTop`, `⊤ = Set.univ`).
//! * `Sup (S :: (β set) set) = ⋃S` ≡ `sSup S = ⋃₀ S` (`Set` `CompleteLattice`);
//!   `Inf (S) = ⋂S` ≡ `sInf S = ⋂₀ S`.
//! * `Fun.inj_on f A` ≡ `Set.InjOn f A` (`∀x∈A,∀y∈A, f x = f y → x = y`).
//! * `Fun.bij_betw f A B` ≡ `Set.BijOn f A B` (`MapsTo ∧ InjOn ∧ SurjOn`).
//!
//! On any non-`Set` carrier `sup`/`inf`/`bot`/`top`/`Sup`/`Inf` are generic
//! lattice operators whose Lean class instance is not statement-determined, so
//! those shapes are declined ([`Unsupported::PolymorphicLattice`]) rather than
//! guessed.

use super::super::super::isabelle_pure::{IsaTerm, IsaType};
use super::super::lean_type::{is_set_of_sets, is_set_type, is_set_typed};
use super::super::term::translate_term;
use super::super::types::{prec, LeanTerm, Unsupported};
use super::{binary_infix, method_object_last, prefix_app};

/// Try to render `n` as a set operator / predicate. `head_ty` is the head
/// constant's own (instantiated) type, consulted only for the nullary `bot`/`top`
/// bounds which carry no argument.
pub(super) fn try_translate(
    n: &str,
    head_ty: &IsaType,
    args: &[&IsaTerm],
) -> Option<Result<LeanTerm, Unsupported>> {
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
        // `card A` → `A.ncard` (`Set.ncard A`; monomorphic `'a set ⇒ nat`).
        "Finite_Set.card" => method_object_last("Finite_Set.card", "ncard", 1, args),
        // `bot :: 'a set` → `∅` / `top :: 'a set` → `Set.univ` (head-type guarded).
        "Orderings.bot_class.bot" => set_bound(n, "∅", head_ty, args),
        "Orderings.top_class.top" => set_bound(n, "Set.univ", head_ty, args),
        // `Sup S` / `Inf S` over a set of sets → `sSup S` / `sInf S`.
        "Complete_Lattices.Sup_class.Sup" => set_of_sets_op(n, "sSup", args),
        "Complete_Lattices.Inf_class.Inf" => set_of_sets_op(n, "sInf", args),
        // `inj_on f A` → `Set.InjOn f A`.
        "Fun.inj_on" => prefix_app("Set.InjOn", 2, args),
        // `bij_betw f A B` → `Set.BijOn f A B`.
        "Fun.bij_betw" => prefix_app("Set.BijOn", 3, args),
        _ => return None,
    };
    Some(out)
}

/// A nullary lattice bound (`bot`/`top`) rendered on a `Set` carrier only. The
/// constant carries no argument, so the guard is on its own head type; off a
/// `Set` carrier the generic lattice bound is not statement-determined and is
/// declined. Any (spurious) application is a shape we do not model.
fn set_bound(
    n: &str,
    lit: &'static str,
    head_ty: &IsaType,
    args: &[&IsaTerm],
) -> Result<LeanTerm, Unsupported> {
    if !args.is_empty() {
        return Err(Unsupported::HigherOrder);
    }
    if !is_set_type(head_ty) {
        return Err(Unsupported::PolymorphicLattice(n.to_string()));
    }
    Ok(LeanTerm::atom(lit))
}

/// The complete-lattice `Sup`/`Inf` (`'a set ⇒ 'a`) rendered on the `Set`
/// instance only: when the operand is a set **of sets** the Isabelle `Sup`/`Inf`
/// is `⋃`/`⋂`, faithfully Mathlib's `sSup`/`sInf` (`⋃₀`/`⋂₀`). On any other
/// complete-lattice carrier the Lean instance is not statement-determined, so the
/// shape is declined.
fn set_of_sets_op(n: &str, head: &'static str, args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [s] = args else {
        return Err(Unsupported::PartialApplication(n.to_string()));
    };
    if !is_set_of_sets(s) {
        return Err(Unsupported::PolymorphicLattice(n.to_string()));
    }
    prefix_app(head, 1, args)
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

    fn tvar() -> IsaType {
        IsaType::TVar {
            n: "'a".into(),
            i: 0,
        }
    }
    fn setty() -> IsaType {
        IsaType::Type {
            n: "Set.set".into(),
            a: vec![tvar()],
        }
    }
    /// A set of sets (`Set.set [Set.set ['a]]`) — the `Sup`/`Inf` `Set` instance.
    fn set_of_setty() -> IsaType {
        IsaType::Type {
            n: "Set.set".into(),
            a: vec![setty()],
        }
    }
    /// A placeholder head-constant type for the arg-guarded shapes (unused there).
    fn any_ty() -> IsaType {
        tvar()
    }
    fn tv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: tvar(),
        }
    }
    fn sv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: setty(),
        }
    }
    fn ssv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: set_of_setty(),
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
        let out = try_translate("Lattices.sup_class.sup", &any_ty(), &[&sv("A"), &sv("B")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "A ∪ B");
    }

    #[test]
    fn nonset_lattice_declined() {
        let x = tv("x");
        assert!(matches!(
            try_translate("Lattices.inf_class.inf", &any_ty(), &[&x, &x]),
            Some(Err(Unsupported::PolymorphicLattice(_)))
        ));
    }

    #[test]
    fn member_is_in() {
        let out = try_translate("Set.member", &any_ty(), &[&tv("x"), &sv("A")])
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
        let out = try_translate("Set.member", &any_ty(), &[&tv("a"), &insert])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "a ∈ insert a B");
    }

    #[test]
    fn image_is_prefix() {
        let out = try_translate("Set.image", &any_ty(), &[&fv("f"), &sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "Set.image f A");
    }

    #[test]
    fn finite_and_card_are_methods() {
        let out = try_translate("Finite_Set.finite", &any_ty(), &[&sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "A.Finite");
        let out = try_translate("Finite_Set.card", &any_ty(), &[&sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "A.ncard");
    }

    #[test]
    fn set_bot_and_top_on_set_carrier() {
        // The nullary bounds guard on their own (instantiated) head type.
        let out = try_translate("Orderings.bot_class.bot", &setty(), &[])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "∅");
        let out = try_translate("Orderings.top_class.top", &setty(), &[])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "Set.univ");
    }

    #[test]
    fn set_bot_off_set_carrier_declined() {
        // `bot :: 'a` on a bare type var → not statement-determined → declined.
        assert!(matches!(
            try_translate("Orderings.bot_class.bot", &tvar(), &[]),
            Some(Err(Unsupported::PolymorphicLattice(_)))
        ));
    }

    #[test]
    fn sup_inf_on_set_of_sets() {
        let out = try_translate("Complete_Lattices.Sup_class.Sup", &any_ty(), &[&ssv("S")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "sSup S");
        let out = try_translate("Complete_Lattices.Inf_class.Inf", &any_ty(), &[&ssv("S")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "sInf S");
    }

    #[test]
    fn sup_off_set_of_sets_declined() {
        // `Sup (A :: 'a set)` where `'a` is not itself a set → generic complete
        // lattice, not statement-determined → declined.
        assert!(matches!(
            try_translate("Complete_Lattices.Sup_class.Sup", &any_ty(), &[&sv("A")]),
            Some(Err(Unsupported::PolymorphicLattice(_)))
        ));
    }

    #[test]
    fn inj_on_and_bij_betw() {
        let out = try_translate("Fun.inj_on", &any_ty(), &[&fv("f"), &sv("A")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "Set.InjOn f A");
        let out = try_translate("Fun.bij_betw", &any_ty(), &[&fv("f"), &sv("A"), &sv("B")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "Set.BijOn f A B");
    }
}
