// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rat Field instance for Environment
//!
//! Contains the Field instance for Rat with all 21 field axioms:
//! - init_rat_field_inst: instFieldRat with add/mul/neg/inv axioms
//! - has_rat_field_inst: initialization check
//!
//! Extracted from `algebra_field.rs` for maintainability.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Rat as a Field instance
    ///
    /// This creates instFieldRat : Field Rat
    /// Rat satisfies all field axioms since every nonzero rational has an inverse.
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.rat_field_inst_init == true`
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_rat_field_inst(&mut self) -> Result<(), EnvError> {
        if self.rat_field_inst_init {
            return Ok(());
        }

        // Initialize dependencies
        self.init_field()?;
        self.init_rat()?;
        self.init_rat_arith()?;
        self.init_int_arith_lemmas()?;

        let rat_type = Expr::const_(Name::from_string("Rat"), vec![]);
        let rat_zero = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let rat_one = Expr::const_(Name::from_string("Rat.one"), vec![]);
        let rat_add = Expr::const_(Name::from_string("Rat.add"), vec![]);
        let rat_mul = Expr::const_(Name::from_string("Rat.mul"), vec![]);
        let rat_neg = Expr::const_(Name::from_string("Rat.neg"), vec![]);
        let rat_inv = Expr::const_(Name::from_string("Rat.inv"), vec![]);

        // Instance type: Field Rat
        // Rat : Type 0, so Field.{0}
        let inst_type = Expr::app(
            Expr::const_(Name::from_string("Field"), vec![Level::zero()]),
            rat_type.clone(),
        );

        // WS-A ATOMIC LIVE SWITCH (step 4, structural commutative-ring laws):
        // `Rat.add_assoc` / `Rat.add_zero` come from the payoff helper below;
        // the other six structural laws (`add_comm`, `zero_add`, `mul_assoc`,
        // `mul_comm`, `one_mul`, `mul_one`) were previously proved over the FREE
        // carrier (relying on its `Rat.add(mk)(mk) ≡ mk(...)` def-eq +
        // `Rat.num`/`Rat.denom` projections). The quotient carrier shifts that
        // def-eq, so they are regenerated as genuine `Quot.ind` + `Quot.sound`
        // proofs (same public name + type) by `register_rat_q_structural`.
        {
            let c = crate::env::algebra_rat_quotient::RatRawConsts::new();
            self.register_rat_q_structural(&c)?;
        }

        // WS-A ATOMIC LIVE SWITCH (step 3, payoff): the structural-equality and
        // order `Rat.*` facts that were FALSE over the free inductive carrier are
        // now GENUINE kernel-checked `Declaration::Theorem`s over the quotient
        // (each `Constructive`, axiom closure ⊆ FOUNDATIONAL via `Quot.sound` /
        // `propext`). This registers, as theorems with the SAME public name +
        // type: `Rat.zero_mul`, `Rat.mul_zero`, `Rat.left_distrib`,
        // `Rat.right_distrib`, `Rat.add_left_neg`, `Rat.add_neg_self`,
        // `Rat.add_right_cancel`, `Rat.mul_inv_cancel`, `Rat.le_antisymm`,
        // `Rat.add_le_add_left`, `Rat.le_add_of_nonneg_right`, plus
        // `Rat.add_zero` / `Rat.add_assoc`. (Formerly seven of these were
        // `Declaration::Axiom`s registered inline here; #3654's bridge-axiom
        // unsoundness is moot now that the carrier is a quotient.)
        self.rat_quotient_payoff_into_live()?;

        // `Rat.mul_comm` is registered as a genuine quotient `Quot.ind` theorem
        // by `register_rat_q_structural` above (it formerly used the free-carrier
        // `register_rat_mul_comm_proof`).

        // Tranche C bridge axiom (#3585) was REMOVED as UNSOUND (#3654).
        // `Rat.mk_eq_mk_of_cross_eq` claimed
        //   ∀ n1 d1 n2 d2. n1*d2 = n2*d1 → Rat.mk n1 d1 = Rat.mk n2 d2
        // but the current Rat carrier is the free inductive
        //   inductive Rat | mk : Int → Nat → Rat
        // not a quotient, so distinct constructor applications such as
        // `Rat.mk 1 2` and `Rat.mk 2 4` are provably unequal by
        // `Rat.noConfusion` even though their Int cross-product is equal.
        // The bridge produced false equalities under the current carrier.
        //
        // Until the quotient-Rat carrier (epic #3470) lands, the downstream
        // Tranche D.1 theorems `Rat.zero_mul`, `Rat.mul_zero`,
        // `Rat.left_distrib` remain honest domain axioms on par with
        // `Rat.right_distrib` above — registered at their respective sites
        // in this module. The bridge, and the constructive proofs that
        // depended on it, have been deleted.

        // `Rat.mul_inv_cancel` and `Rat.add_right_cancel` are registered as
        // genuine quotient theorems by `rat_quotient_payoff_into_live()` above
        // (they were formerly inline `Declaration::Axiom`s here).

        // inv_zero : inv zero = zero (by convention)
        //
        // Phase 1 of #3581 (Tranche B): promoted from `Declaration::Axiom`
        // to `Declaration::Theorem` with a genuine kernel-checked proof term
        // (`Eq.refl` — the reducible `Rat.inv` definition collapses
        // `Rat.inv Rat.zero` to `Rat.zero` via pure delta+iota). See
        // `algebra_rat_tranche_b_proofs.rs` for the proof body and
        // `reports/audit/2026-04-20-rat-field-axiom-triage.md` for the
        // tranche classification.
        self.register_rat_inv_zero_proof()?;

        // Now build the Field.mk application with all 21 fields
        // Field.mk {α} add add_assoc zero zero_add add_zero add_comm
        //          mul mul_assoc one one_mul mul_one zero_mul mul_zero
        //          left_distrib right_distrib neg add_left_neg inv mul_inv_cancel inv_zero mul_comm

        let inst_value = {
            // Rat : Type 0, so Field.mk.{0}
            let mk = Expr::const_(Name::from_string("Field.mk"), vec![Level::zero()]);

            // Get proof constants
            let rat_add_assoc = Expr::const_(Name::from_string("Rat.add_assoc"), vec![]);
            let rat_zero_add = Expr::const_(Name::from_string("Rat.zero_add"), vec![]);
            let rat_add_zero = Expr::const_(Name::from_string("Rat.add_zero"), vec![]);
            let rat_add_comm_proof = Expr::const_(Name::from_string("Rat.add_comm"), vec![]);
            let rat_mul_assoc = Expr::const_(Name::from_string("Rat.mul_assoc"), vec![]);
            let rat_one_mul = Expr::const_(Name::from_string("Rat.one_mul"), vec![]);
            let rat_mul_one_proof = Expr::const_(Name::from_string("Rat.mul_one"), vec![]);
            let rat_zero_mul = Expr::const_(Name::from_string("Rat.zero_mul"), vec![]);
            let rat_mul_zero_proof = Expr::const_(Name::from_string("Rat.mul_zero"), vec![]);
            let rat_left_distrib = Expr::const_(Name::from_string("Rat.left_distrib"), vec![]);
            let rat_right_distrib = Expr::const_(Name::from_string("Rat.right_distrib"), vec![]);
            let rat_add_left_neg_proof =
                Expr::const_(Name::from_string("Rat.add_left_neg"), vec![]);
            let rat_mul_inv_cancel = Expr::const_(Name::from_string("Rat.mul_inv_cancel"), vec![]);
            let rat_inv_zero = Expr::const_(Name::from_string("Rat.inv_zero"), vec![]);
            let rat_mul_comm_proof = Expr::const_(Name::from_string("Rat.mul_comm"), vec![]);

            // Apply mk to Rat type and all operations/proofs
            let e = Expr::app(mk, rat_type.clone());
            let e = Expr::app(e, rat_add);
            let e = Expr::app(e, rat_add_assoc);
            let e = Expr::app(e, rat_zero);
            let e = Expr::app(e, rat_zero_add);
            let e = Expr::app(e, rat_add_zero);
            let e = Expr::app(e, rat_add_comm_proof);
            let e = Expr::app(e, rat_mul);
            let e = Expr::app(e, rat_mul_assoc);
            let e = Expr::app(e, rat_one);
            let e = Expr::app(e, rat_one_mul);
            let e = Expr::app(e, rat_mul_one_proof);
            let e = Expr::app(e, rat_zero_mul);
            let e = Expr::app(e, rat_mul_zero_proof);
            let e = Expr::app(e, rat_left_distrib);
            let e = Expr::app(e, rat_right_distrib);
            let e = Expr::app(e, rat_neg);
            let e = Expr::app(e, rat_add_left_neg_proof);
            let e = Expr::app(e, rat_inv);
            let e = Expr::app(e, rat_mul_inv_cancel);
            let e = Expr::app(e, rat_inv_zero);
            Expr::app(e, rat_mul_comm_proof)
        };

        self.add_decl(Declaration::Definition {
            name: Name::from_string("instFieldRat"),
            level_params: vec![],
            type_: inst_type,
            value: inst_value,
            is_reducible: true,
        })?;

        self.rat_field_inst_init = true;
        Ok(())
    }

    /// Check if Rat Field instance has been initialized
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: Returns `true` iff `self.rat_field_inst_init == true`
    pub(crate) fn has_rat_field_inst(&self) -> bool {
        self.rat_field_inst_init
    }
}
