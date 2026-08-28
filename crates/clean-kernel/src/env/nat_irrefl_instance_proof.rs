// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive demotion of `instIrreflNatLt` from `Declaration::Axiom` to a
//! kernel-checked `Declaration::Definition`.
//!
//! `instIrreflNatLt : Irrefl.{1} Nat (fun a b => a < b)` was one of the six
//! ASSERTED PROPOSITIONS the default prelude shipped as axioms
//! (`debt_proposition` in `data/prelude_axiom_ratchet.json`). Unlike the other
//! five it is not a lemma at all — it is a typeclass *instance*, and the lemma
//! it carries, `Nat.lt_irrefl`, has been a constructive `Declaration::Theorem`
//! since `nat_lt_irrefl_proof.rs` landed. `order.rs::init_nat_lt_irrefl` was
//! already registering that theorem three lines above asserting the instance
//! over it.
//!
//! # Proof
//!
//! `Irrefl` is a genuine single-field Prop class
//! (`order_relation_props.rs::init_irrefl`), so the instance is just its
//! constructor applied to the field:
//!
//! ```text
//! instIrreflNatLt : Irrefl.{1} Nat (fun a b => LT.lt Nat instLTNat a b)
//!   := Irrefl.mk.{1} Nat (fun a b => LT.lt Nat instLTNat a b) Nat.lt_irrefl
//! ```
//!
//! `Irrefl.mk`'s field argument is `∀ x : α, r x x → False`; at
//! `r := fun a b => LT.lt Nat instLTNat a b` that beta-reduces to
//! `∀ x, LT.lt Nat instLTNat x x → False`, and `LT.lt`/`instLTNat` are
//! reducible projections onto `Nat.lt`, so `Nat.lt_irrefl` is accepted
//! definitionally with no wrapper lambda.
//!
//! # Why a `Definition` and not a `Theorem`
//!
//! Instances are `def`s in Lean, and the sibling relation instances this
//! prelude registers (`instLTNat`, `instLENat`, `Irrefl.irrefl`) are
//! `Declaration::Definition`s. The declaration is still fully kernel-checked —
//! `add_decl` type-checks a `Definition`'s value against its type exactly as it
//! does a `Theorem`'s — so the axiom is retired either way; `Definition` simply
//! keeps the instance resolvable and unfoldable the way every other instance in
//! the prelude is. It is NOT `is_reducible`: nothing should unfold an instance
//! of a `Prop`-valued class during conversion.
//!
//! The legacy axiom site in `order.rs::init_nat_lt_irrefl` is now guarded by a
//! `get_const` check, so it is an idempotent no-op once this definition is
//! present.

use super::order::nat_lt_relation;
use super::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Register `instIrreflNatLt` as a kernel-checked instance built from the
    /// constructive `Nat.lt_irrefl`.
    ///
    /// Idempotent: a no-op when the name is already present.
    ///
    /// # Errors
    ///
    /// Propagates any `EnvError` from the dependency initializers or from
    /// `add_decl`'s kernel check of the instance value.
    pub(crate) fn register_nat_irrefl_instance(&mut self) -> Result<(), EnvError> {
        let name = Name::from_string("instIrreflNatLt");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        self.init_nat()?;
        self.init_lt()?;
        self.init_true_false()?;
        self.init_irrefl()?;
        self.register_nat_lt_irrefl_theorem()?;

        // `Nat : Type 0 = Sort 1`, so `Irrefl`/`Irrefl.mk` instantiate at `u := 1`.
        let nat_sort = Level::succ(Level::zero());
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let relation = nat_lt_relation();

        let type_ = Expr::apps(
            Expr::const_(Name::from_string("Irrefl"), vec![nat_sort.clone()]),
            [nat.clone(), relation.clone()],
        );
        let value = Expr::apps(
            Expr::const_(Name::from_string("Irrefl.mk"), vec![nat_sort]),
            [
                nat,
                relation,
                Expr::const_(Name::from_string("Nat.lt_irrefl"), vec![]),
            ],
        );

        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_,
            value,
            is_reducible: false,
        })
    }
}
