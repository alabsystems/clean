// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! General n-row constructive Farkas combination over a `List` of rows.
//!
//! Generalizes the two-row `NNVerify.farkas_combine_2` (in
//! `nn_verify_foundation_theorems_farkas_constructive.rs`) to an arbitrary
//! number of rows, folded with `List.rec`. This closes the arithmetic core
//! of the still-axiomatized `farkas_to_interval`: a non-negative
//! multiplier combination of N premise inequalities preserves the bound.
//!
//! ## Encoding
//!
//! A single Farkas row carries `(mu, a, b)` packed as a nested product
//!   `Row := Prod Rat (Prod Rat Rat)`  (`Rat : Type 0`, so `Row : Type 0`).
//! The rows are a `List Row`.
//!
//! Three reducible `List.rec` definitions fold the list:
//! - `NNVerify.farkasLower rows = Σ mu_i * a_i`   (foldr with `Rat.add`, base `Rat.zero`)
//! - `NNVerify.farkasUpper rows = Σ mu_i * b_i`   (foldr with `Rat.add`, base `Rat.zero`)
//! - `NNVerify.farkasRowsValid rows = ⋀ (0 ≤ mu_i ∧ a_i ≤ b_i)` (foldr-And, base `True`)
//!
//! ## Theorem
//!
//! `NNVerify.farkas_combine_list :
//!    ∀ (rows : List Row), farkasRowsValid rows → farkasLower rows ≤ farkasUpper rows`
//!
//! ## Proof strategy (constructive, zero sorry)
//!
//! `List.rec @{0,0}` with motive `fun rows => farkasRowsValid rows →
//! farkasLower rows ≤ farkasUpper rows`.
//!
//! - **nil**: `farkasLower [] = 0`, `farkasUpper [] = 0`; conclusion is
//!   `0 ≤ 0`, discharged by `Rat.le_refl Rat.zero` (ignoring the `True`
//!   validity hypothesis).
//! - **cons** `(row :: tail)`: the validity hypothesis is
//!   `And (0 ≤ mu ∧ a ≤ b) (farkasRowsValid tail)`. Decompose with
//!   `And.left`/`And.right`. The head bound `mu*a ≤ mu*b` is exactly
//!   `mul_nonneg_le_left mu a b hmu hab` (the `c.scale` helper); the tail
//!   bound `farkasLower tail ≤ farkasUpper tail` comes from the inductive
//!   hypothesis applied to `And.right`. Combine the two with
//!   `add_le_add (mu*a) (mu*b) (Σtail_lo) (Σtail_hi)` (the `c.add_le`
//!   helper) — literally `farkas_combine_2` with the folded tail sum.
//!
//! Reuses the shared `FarkasConsts` term builders (`scale`, `add_le`,
//! `rat_le`, `add`, `mul`) from
//! `nn_verify_foundation_theorems_farkas_constructive_proofs.rs`.
//!
//! The transitive axiom closure references only honest `Rat`
//! ordered-field axioms (`Rat.le_refl`, plus those under
//! `mul_nonneg_le_left` / `add_le_add`); it does NOT depend on
//! `farkas_certificate_valid` or any opaque/sorry predicate.

use crate::env::nn_verify_farkas_list_proofs::{
    build_combine_list_proof, build_combine_list_type, build_fold_type, build_fold_value,
    build_valid_type, build_valid_value, FarkasListConsts,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize the general n-row constructive Farkas combination.
    ///
    /// Depends on: `init_nn_verify_farkas_constructive` (which provides
    /// `mul_nonneg_le_left` / `add_le_add` via foundation theorems), plus
    /// `init_list`, `init_prod`, `init_and`, `init_true_false`, and
    /// `init_rat_linear_order` (for `Rat.le_refl`).
    ///
    /// # Contract
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `farkasLower`, `farkasUpper`, `farkasRowsValid`
    ///          registered as reducible `Declaration::Definition`s, and
    ///          `farkas_combine_list` as a constructive `Declaration::Theorem`
    /// ENSURES: Idempotent
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_nn_verify_farkas_list(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_farkas_list_init {
            return Ok(());
        }
        self.init_nn_verify_farkas_constructive()?;
        self.init_list()?;
        self.init_prod()?;
        self.init_and()?;
        self.init_true_false()?;
        self.init_rat_linear_order()?;

        let c = FarkasListConsts::new();
        self.register_farkas_lower(&c)?;
        self.register_farkas_upper(&c)?;
        self.register_farkas_rows_valid(&c)?;
        self.register_farkas_combine_list(&c)?;

        self.nn_verify_farkas_list_init = true;
        Ok(())
    }

    fn register_farkas_lower(&mut self, c: &FarkasListConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkasLower");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_fold_type(c),
            value: build_fold_value(c, false),
            is_reducible: true,
        })
    }

    fn register_farkas_upper(&mut self, c: &FarkasListConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkasUpper");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_fold_type(c),
            value: build_fold_value(c, true),
            is_reducible: true,
        })
    }

    fn register_farkas_rows_valid(&mut self, c: &FarkasListConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkasRowsValid");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_valid_type(c),
            value: build_valid_value(c),
            is_reducible: true,
        })
    }

    fn register_farkas_combine_list(&mut self, c: &FarkasListConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkas_combine_list");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_combine_list_type(c),
            value: build_combine_list_proof(c),
        })
    }
}

#[cfg(test)]
mod tests {
    use crate::env::types::ConstantKind;
    use crate::env::Environment;
    use crate::expr::{Expr, ExprKind};
    use crate::name::Name;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_farkas_list()
            .expect("init_nn_verify_farkas_list");
        env
    }

    /// A reducible definition: registered, has a value, value type-checks
    /// against the declared type, and is sorry-free.
    fn assert_definition(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        let val = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have a value"));
        assert!(
            !info.sorry_summary().has_sorry,
            "{name} should be sorry-free"
        );
        let tc = TypeChecker::with_mode(env, env.mode());
        let inferred = tc
            .infer_type(val)
            .unwrap_or_else(|e| panic!("{name} value should type-check, got {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name}: inferred type should match declared type"
        );
    }

    #[test]
    fn test_farkas_lower_definition() {
        assert_definition(&make_env(), "NNVerify.farkasLower");
    }

    #[test]
    fn test_farkas_upper_definition() {
        assert_definition(&make_env(), "NNVerify.farkasUpper");
    }

    #[test]
    fn test_farkas_rows_valid_definition() {
        assert_definition(&make_env(), "NNVerify.farkasRowsValid");
    }

    #[test]
    fn test_farkas_combine_list_constructive() {
        let env = make_env();
        let name = "NNVerify.farkas_combine_list";
        let info = env
            .get_const(&Name::from_string(name))
            .expect("farkas_combine_list should be registered");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be a Theorem"
        );
        let proof = info.value.as_ref().expect("should have a proof term");
        assert!(
            !info.sorry_summary().has_sorry,
            "{name} proof should be sorry-free"
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc
            .infer_type(proof)
            .unwrap_or_else(|e| panic!("{name} proof should type-check, got {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name}: inferred type should match declared type"
        );
        assert!(
            matches!(info.type_.kind(), ExprKind::Pi(..)),
            "{name} type should be a Pi"
        );
        // The const itself must also infer (validates the whole declaration).
        let _ = tc
            .infer_type(&Expr::const_(Name::from_string(name), vec![]))
            .unwrap_or_else(|e| panic!("{name} const should type-check, got {e:?}"));
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_farkas_list().expect("first");
        env.init_nn_verify_farkas_list().expect("second");
    }

    /// End-to-end: applying `farkas_combine_list` to a concrete two-row
    /// list type-checks, and the conclusion's `farkasLower`/`farkasUpper`
    /// iota-reduce through `List.rec` to the expected concrete sums. This
    /// exercises the actual computational content of the fold definitions,
    /// not just the abstract Pi shape.
    #[test]
    fn test_concrete_two_row_instance_reduces_and_applies() {
        use crate::level::Level;
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());

        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let zero = Level::zero();
        let prod = Expr::const_(Name::from_string("Prod"), vec![zero.clone(), zero.clone()]);
        let prod_mk = Expr::const_(
            Name::from_string("Prod.mk"),
            vec![zero.clone(), zero.clone()],
        );
        let pair_ty = Expr::app(Expr::app(prod.clone(), rat.clone()), rat.clone());
        let row_ty = Expr::app(Expr::app(prod.clone(), rat.clone()), pair_ty.clone());
        let list_cons = Expr::const_(Name::from_string("List.cons"), vec![zero.clone()]);
        let list_nil = Expr::const_(Name::from_string("List.nil"), vec![zero.clone()]);

        // Build a row (mu, a, b) as Prod.mk mu (Prod.mk a b).
        let mk_row = |mu: Expr, a: Expr, b: Expr| {
            let pair = Expr::apps(prod_mk.clone(), [rat.clone(), rat.clone(), a, b]);
            Expr::apps(prod_mk.clone(), [rat.clone(), pair_ty.clone(), mu, pair])
        };

        // Use Rat.zero as the concrete rational in each slot.
        let r0 = Expr::const_(Name::from_string("Rat.zero"), vec![]);
        let row1 = mk_row(r0.clone(), r0.clone(), r0.clone());
        let row2 = mk_row(r0.clone(), r0.clone(), r0.clone());

        // rows = row1 :: row2 :: []
        let nil = Expr::app(list_nil, row_ty.clone());
        let l1 = Expr::apps(list_cons.clone(), [row_ty.clone(), row2, nil]);
        let rows = Expr::apps(list_cons, [row_ty.clone(), row1, l1]);

        // farkasRowsValid rows must be a well-formed Prop.
        let valid = Expr::app(
            Expr::const_(Name::from_string("NNVerify.farkasRowsValid"), vec![]),
            rows.clone(),
        );
        let valid_ty = tc
            .infer_type(&valid)
            .expect("farkasRowsValid <concrete> should type-check");
        assert!(
            tc.is_def_eq(&valid_ty, &Expr::sort(Level::zero())),
            "farkasRowsValid <concrete> : Prop"
        );

        // farkasLower rows and farkasUpper rows must be Rats.
        for fold in ["NNVerify.farkasLower", "NNVerify.farkasUpper"] {
            let app = Expr::app(Expr::const_(Name::from_string(fold), vec![]), rows.clone());
            let t = tc
                .infer_type(&app)
                .unwrap_or_else(|e| panic!("{fold} <concrete> should type-check: {e:?}"));
            assert!(tc.is_def_eq(&t, &rat), "{fold} <concrete> : Rat");
        }

        // Partially apply the theorem to the concrete list: the result is a
        // function `farkasRowsValid rows → farkasLower rows ≤ farkasUpper rows`.
        let thm = Expr::const_(Name::from_string("NNVerify.farkas_combine_list"), vec![]);
        let applied = Expr::app(thm, rows.clone());
        let applied_ty = tc
            .infer_type(&applied)
            .expect("farkas_combine_list <concrete> should type-check");
        // It must be a Pi (the validity hypothesis).
        assert!(
            matches!(applied_ty.kind(), ExprKind::Pi(..)),
            "applied theorem should still expect the validity hypothesis"
        );
    }
}
