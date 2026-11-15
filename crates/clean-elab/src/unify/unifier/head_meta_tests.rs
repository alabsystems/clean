// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathlib-free regression for the srcelab row `Prod.mk_lt_mk`
//! (`Mathlib/Order/Basic.lean`): a product order whose `<` is a field of a
//! derived instance, and a lemma whose right side projects the pair the left
//! side assigns. Pinned Lean 4.8.0 accepts `mk_lt_mk := lt_iff` and refuses
//! the twin with a swapped strict side ("type mismatch"). Before the head read
//! in `try_whnf`, Clean refused the original with "Type mismatch … got ?x <
//! ?y ↔ …" (the probe budget spent on `?x.1 =?= a₁`, `head_meta.rs`).

use clean_kernel::Environment;

const SETUP: &str = "class MyPreorder (α : Type) extends LE α, LT α where\n  \
     le_refl : ∀ a : α, a ≤ a\n\
     instance MyProd.instPre {α β : Type} [MyPreorder α] [MyPreorder β] : MyPreorder (α × β) where\n  \
     le p q := p.1 ≤ q.1 ∧ p.2 ≤ q.2\n  \
     lt p q := (p.1 ≤ q.1 ∧ p.2 ≤ q.2) ∧ ¬ (q.1 ≤ p.1 ∧ q.2 ≤ p.2)\n  \
     le_refl := fun p => ⟨MyPreorder.le_refl p.1, MyPreorder.le_refl p.2⟩\n\
     axiom MyProd.lt_iff {α β : Type} [MyPreorder α] [MyPreorder β] {x y : α × β} :\n    \
     x < y ↔ x.1 < y.1 ∧ x.2 ≤ y.2 ∨ x.1 ≤ y.1 ∧ x.2 < y.2\n";

fn elab(src: &str) -> Result<(), String> {
    let mut env = Environment::with_prelude();
    for decl in clean_parser::parse_file(src).map_err(|e| format!("parse: {e:?}"))? {
        crate::elaborate_decl_and_register_with_warning(&mut env, &decl)
            .map_err(|e| format!("{e}"))?;
    }
    Ok(())
}

#[test]
fn test_assigned_pair_is_projected_within_one_unification() {
    let accepted = format!(
        "{SETUP}theorem MyProd.mk_lt_mk {{α β : Type}} [MyPreorder α] [MyPreorder β] \
         {{a₁ a₂ : α}} {{b₁ b₂ : β}} :\n    \
         (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₁ < b₂ :=\n  MyProd.lt_iff\n"
    );
    elab(&accepted).unwrap_or_else(|e| panic!("pinned Lean 4.8.0 accepts this: {e}"));
    let twin = format!(
        "{SETUP}theorem MyProd.mk_lt_mk_twin {{α β : Type}} [MyPreorder α] [MyPreorder β] \
         {{a₁ a₂ : α}} {{b₁ b₂ : β}} :\n    \
         (a₁, b₁) < (a₂, b₂) ↔ a₁ < a₂ ∧ b₁ ≤ b₂ ∨ a₁ ≤ a₂ ∧ b₂ < b₁ :=\n  MyProd.lt_iff\n"
    );
    let e = elab(&twin).expect_err("pinned Lean 4.8.0 refuses the swapped strict side");
    assert!(e.contains("mismatch"), "refused as a type mismatch: {e}");
}
