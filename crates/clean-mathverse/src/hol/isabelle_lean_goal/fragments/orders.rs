// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Order fragment. The comparisons `≤`/`<`/`≥`/`>` render on two faithful
//! carriers:
//! * a **concrete numeric** type (`ℕ`, `ℤ`, `ℚ`, `ℝ`) whose Lean order instance
//!   is unambiguous → `≤ < ≥ >`;
//! * a **`Set`** operand, where Isabelle's order *is* the subset order → `⊆ ⊂ ⊇
//!   ⊃` (`A ≤ B ⟷ A ⊆ B`, `A < B ⟷ A ⊂ B` for `'a set`, matching Mathlib's
//!   `Set` `LE`/`LT` instances).
//!
//! Over a bare type variable the correct Lean order class
//! (`Preorder`/`PartialOrder`/`LinearOrder`) is not determined by the statement,
//! so the shape is declined ([`Unsupported::PolymorphicOrder`]) — the
//! faithfulness boundary that keeps class-heavy order lemmas in the human/agent
//! curation tail rather than emitting a guessed typeclass binder.
//!
//! `max`/`min` render `max a b`/`min a b` on the same concrete-numeric guard
//! (Lean `Max`/`Min` via `LinearOrder`); off a concrete carrier they are
//! declined for the same class-ambiguity reason.

use super::super::super::isabelle_pure::IsaTerm;
use super::super::lean_type::{is_concrete_ordered, is_set_typed};
use super::super::types::{prec, LeanTerm, Unsupported};
use super::{binary_infix, prefix_app};

/// Try to render `n` as an order comparison or `max`/`min`.
pub(super) fn try_translate(n: &str, args: &[&IsaTerm]) -> Option<Result<LeanTerm, Unsupported>> {
    // (numeric op, set-subset op) pairs.
    let ops = match n {
        "Orderings.ord_class.less_eq" => ("≤", "⊆"),
        "Orderings.ord_class.less" => ("<", "⊂"),
        "Orderings.ord_class.greater_eq" => ("≥", "⊇"),
        "Orderings.ord_class.greater" => (">", "⊃"),
        "Orderings.ord_class.max" => return Some(minmax(n, "max", args)),
        "Orderings.ord_class.min" => return Some(minmax(n, "min", args)),
        _ => return None,
    };
    Some(order_binop(n, ops.0, ops.1, args))
}

/// A relation, rendered `≤/<` on a concrete numeric operand or `⊆/⊂` on a `Set`
/// operand; declined on a bare type variable.
fn order_binop(
    n: &str,
    num_op: &'static str,
    set_op: &'static str,
    args: &[&IsaTerm],
) -> Result<LeanTerm, Unsupported> {
    let [l, _] = args else {
        return Err(Unsupported::PartialApplication(n.to_string()));
    };
    let op = if is_set_typed(l) {
        set_op
    } else if is_concrete_ordered(l) {
        num_op
    } else {
        return Err(Unsupported::PolymorphicOrder);
    };
    binary_infix(n, op, prec::REL, args)
}

/// `max a b` / `min a b`, guarded to a concrete numeric operand (Lean `Max`/`Min`
/// via the type's `LinearOrder`); declined off a concrete carrier.
fn minmax(n: &str, head: &'static str, args: &[&IsaTerm]) -> Result<LeanTerm, Unsupported> {
    let [l, _] = args else {
        return Err(Unsupported::PartialApplication(n.to_string()));
    };
    if !is_concrete_ordered(l) {
        return Err(Unsupported::PolymorphicOrder);
    }
    prefix_app(head, 2, args)
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
    fn nv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: nat(),
        }
    }
    fn sv(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: IsaType::Type {
                n: "Set.set".into(),
                a: vec![IsaType::TVar {
                    n: "'a".into(),
                    i: 0,
                }],
            },
        }
    }
    fn av(n: &str) -> IsaTerm {
        IsaTerm::Var {
            n: n.into(),
            i: 0,
            t: IsaType::TVar {
                n: "'a".into(),
                i: 0,
            },
        }
    }

    #[test]
    fn nat_le_renders() {
        let out = try_translate("Orderings.ord_class.less_eq", &[&nv("i"), &nv("j")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "i ≤ j");
    }

    #[test]
    fn set_le_is_subseteq() {
        let out = try_translate("Orderings.ord_class.less_eq", &[&sv("A"), &sv("B")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "A ⊆ B");
        let out = try_translate("Orderings.ord_class.less", &[&sv("A"), &sv("B")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "A ⊂ B");
    }

    #[test]
    fn polymorphic_le_declined() {
        assert!(matches!(
            try_translate("Orderings.ord_class.less_eq", &[&av("x"), &av("x")]),
            Some(Err(Unsupported::PolymorphicOrder))
        ));
    }

    #[test]
    fn concrete_max_renders_and_polymorphic_declined() {
        let out = try_translate("Orderings.ord_class.max", &[&nv("x"), &nv("y")])
            .unwrap()
            .unwrap();
        assert_eq!(render_top(&out), "max x y");
        assert!(matches!(
            try_translate("Orderings.ord_class.min", &[&av("x"), &av("y")]),
            Some(Err(Unsupported::PolymorphicOrder))
        ));
    }
}
