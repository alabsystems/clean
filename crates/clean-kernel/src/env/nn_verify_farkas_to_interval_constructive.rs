// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Constructive successor to the legacy `NNVerify.farkas_to_interval` AXIOM.
//!
//! ## Why the legacy axiom could not be discharged
//!
//! The legacy `NNVerify.farkas_to_interval` (in
//! `nn_verify_foundation_theorems_farkas.rs`) is a `Declaration::Axiom`
//! whose hypothesis `NNVerify.farkas_certificate_valid` is *itself* an
//! opaque `Declaration::Axiom` predicate
//! (`(d : Nat) → NNVec d → Rat → IntervalBounds d → Prop`) with **no
//! computational content**. There is nothing to eliminate from an opaque
//! predicate, so no constructive proof term can inhabit that exact
//! statement. (The legacy axiom is retained, unchanged, so existing
//! consumers/tests keep working; it is superseded — "demoted" — by the
//! constructive declarations registered here, which the cert parser and
//! downstream proofs should prefer.)
//!
//! ## What is constructive here
//!
//! Over the same `List Row = (mu, a, b)` representation used by the
//! sorry-free n-row combination `NNVerify.farkas_combine_list`
//! (`nn_verify_farkas_list.rs`), this module registers:
//!
//! 1. `NNVerify.farkasCertificateValid` — a **real** reducible
//!    `Declaration::Definition` (NOT an axiom):
//!      `farkasCertificateValid (rows : List Row) (bound : Rat) : Prop
//!         := And (farkasRowsValid rows) (farkasUpper rows ≤ bound)`.
//!    It carries genuine computational content: the per-row premises
//!    `farkasRowsValid rows` (each `0 ≤ muᵢ ∧ aᵢ ≤ bᵢ`) AND the
//!    dominating-constant condition `farkasUpper rows ≤ bound`
//!    (`Σ muᵢ·bᵢ ≤ bound`). A proof can `And.left`/`And.right`-eliminate it.
//!
//! 2. `NNVerify.farkas_to_interval_constructive` — a constructive
//!    `Declaration::Theorem` (NOT an axiom):
//!      `∀ (rows : List Row) (bound : Rat),
//!         farkasCertificateValid rows bound → farkasLower rows ≤ bound`.
//!    Proof: `Rat.le_trans (farkasLower rows) (farkasUpper rows) bound
//!              (@farkas_combine_list rows (And.left hcert))
//!              (And.right hcert)` — the n-row combination
//!    `farkas_combine_list` (`farkasLower ≤ farkasUpper`) chained with the
//!    certificate's dominating bound (`farkasUpper ≤ bound`). This is
//!    exactly "a valid Farkas certificate implies the claimed bound",
//!    reduced to `farkas_combine_list` + the real `farkasCertificateValid`
//!    definition. `TypeChecker::infer_type` accepts it, `is_def_eq` confirms
//!    the type, and it is `!has_sorry`.
//!
//! ## Scope of the constructive result (ruthless honesty)
//!
//! The conclusion is `farkasLower rows ≤ bound`, where `farkasLower` is the
//! `List.rec` fold `Σ muᵢ·aᵢ`. The legacy axiom's conclusion was
//! `NNVec.dot d cv x ≤ bound`, where `NNVec.dot` is the *separate*
//! `Fin.sum`-based dot product. Bridging the `Fin.sum` dot product to the
//! `List`-fold `farkasLower` is an orthogonal `Fin.sum`↔`List.foldr` lemma
//! and is **not** part of this theorem; that opaque glue
//! (`NNVec.dot`/`IntervalBounds`) remains isolated in the legacy axiom. What
//! IS now constructive and kernel-checked is the Farkas arithmetic core: a
//! non-negative multiplier combination of N premise inequalities, dominated
//! by a constant, bounds the combined linear form by that constant.
//!
//! The proof-term/type builders and `FarkasToIntervalConsts` live in
//! `nn_verify_farkas_to_interval_constructive_proofs.rs` to keep this module
//! under the 500-line limit (mirroring the `nn_verify_farkas_list` split).

use crate::env::nn_verify_farkas_to_interval_constructive_proofs::{
    build_cert_valid_type, build_cert_valid_value, build_to_interval_proof, build_to_interval_type,
    FarkasToIntervalConsts,
};
use crate::env::{Declaration, EnvError, Environment};
use crate::name::Name;

impl Environment {
    /// Initialize the constructive Farkas-to-bound declarations.
    ///
    /// Depends on: `init_nn_verify_farkas_list` (which provides
    /// `farkasLower` / `farkasUpper` / `farkasRowsValid` /
    /// `farkas_combine_list`), plus `init_and` (And/And.left/And.right) and
    /// `init_rat_linear_order` (`Rat.le_trans`), both already pulled in
    /// transitively by `init_nn_verify_farkas_list`.
    ///
    /// # Contract
    /// REQUIRES: `self` is a valid Environment
    /// ENSURES: On success, `farkasCertificateValid` registered as a
    ///          reducible `Declaration::Definition`, and
    ///          `farkas_to_interval_constructive` as a constructive,
    ///          sorry-free `Declaration::Theorem`
    /// ENSURES: Idempotent
    #[cfg(any(test, feature = "math-overlays"))]
    pub fn init_nn_verify_farkas_to_interval_constructive(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_farkas_to_interval_constructive_init {
            return Ok(());
        }
        self.init_nn_verify_farkas_list()?;

        let c = FarkasToIntervalConsts::new();
        self.register_farkas_certificate_valid_def(&c)?;
        self.register_farkas_to_interval_constructive(&c)?;

        self.nn_verify_farkas_to_interval_constructive_init = true;
        Ok(())
    }

    /// Register `NNVerify.farkasCertificateValid` as a reducible definition:
    /// `fun rows bound => And (farkasRowsValid rows) (farkasUpper rows ≤ bound)`.
    fn register_farkas_certificate_valid_def(
        &mut self,
        c: &FarkasToIntervalConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkasCertificateValid");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Definition {
            name,
            level_params: vec![],
            type_: build_cert_valid_type(c),
            value: build_cert_valid_value(c),
            is_reducible: true,
        })
    }

    /// Register `NNVerify.farkas_to_interval_constructive` as a constructive
    /// theorem reducing to `farkas_combine_list` + `Rat.le_trans`.
    fn register_farkas_to_interval_constructive(
        &mut self,
        c: &FarkasToIntervalConsts,
    ) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.farkas_to_interval_constructive");
        if self.get_const(&name).is_some() {
            return Ok(());
        }
        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: build_to_interval_type(c),
            value: build_to_interval_proof(c),
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
        env.init_nn_verify_farkas_to_interval_constructive()
            .expect("init_nn_verify_farkas_to_interval_constructive");
        env
    }

    /// A reducible definition: registered, is a Definition, has a value, the
    /// value type-checks against the declared type, and is sorry-free.
    #[test]
    fn test_farkas_certificate_valid_is_real_definition() {
        let env = make_env();
        let name = "NNVerify.farkasCertificateValid";
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Definition,
            "{name} should be a real Definition (not an Axiom), got {:?}",
            info.kind
        );
        let val = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have a value (computational content)"));
        assert!(
            !info.sorry_summary().has_sorry,
            "{name} should be sorry-free"
        );
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc
            .infer_type(val)
            .unwrap_or_else(|e| panic!("{name} value should type-check, got {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name}: inferred type should match declared type"
        );
    }

    /// The decisive assertion: `farkas_to_interval_constructive` is a
    /// Theorem (NOT an Axiom), its proof term `infer_type`s Ok, `is_def_eq`
    /// matches the declared type, and the declaration is `!has_sorry`.
    #[test]
    fn test_farkas_to_interval_constructive_is_sorry_free_theorem() {
        let env = make_env();
        let name = "NNVerify.farkas_to_interval_constructive";
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} should be a Theorem (not an Axiom), got {:?}",
            info.kind
        );
        let proof = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} should have a proof term"));
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

    /// The proof genuinely reduces to the constructive n-row combination
    /// `farkas_combine_list` (not the legacy axiom).
    #[test]
    fn test_proof_is_backed_by_farkas_combine_list() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string(
                "NNVerify.farkas_to_interval_constructive",
            ))
            .expect("should be registered");
        let proof = info.value.as_ref().expect("should have proof term");
        assert!(
            mentions_const(proof, "NNVerify.farkas_combine_list"),
            "proof must be backed by the sorry-free n-row combination \
             NNVerify.farkas_combine_list"
        );
        assert!(
            !mentions_const(proof, "NNVerify.farkas_to_interval")
                || mentions_const(proof, "NNVerify.farkas_to_interval_constructive"),
            "proof must NOT depend on the legacy NNVerify.farkas_to_interval axiom"
        );
        // farkas_combine_list it references is itself a sorry-free Theorem.
        let combine = env
            .get_const(&Name::from_string("NNVerify.farkas_combine_list"))
            .expect("farkas_combine_list must be registered");
        assert_eq!(combine.kind, ConstantKind::Theorem);
        assert!(!combine.sorry_summary().has_sorry);
    }

    /// End-to-end: applying the theorem to a concrete two-row list type-checks
    /// and still expects the certificate hypothesis, exercising the actual
    /// computational content of `farkasCertificateValid` / the folds.
    #[test]
    fn test_concrete_two_row_instance_applies() {
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
        let r0 = Expr::const_(Name::from_string("Rat.zero"), vec![]);

        let mk_row = |mu: Expr, a: Expr, b: Expr| {
            let inner = Expr::apps(prod_mk.clone(), [rat.clone(), rat.clone(), a, b]);
            Expr::apps(prod_mk.clone(), [rat.clone(), pair_ty.clone(), mu, inner])
        };
        let row1 = mk_row(r0.clone(), r0.clone(), r0.clone());
        let row2 = mk_row(r0.clone(), r0.clone(), r0.clone());
        let nil = Expr::app(list_nil, row_ty.clone());
        let l1 = Expr::apps(list_cons.clone(), [row_ty.clone(), row2, nil]);
        let rows = Expr::apps(list_cons, [row_ty.clone(), row1, l1]);

        // farkasCertificateValid rows Rat.zero : Prop.
        let cert = Expr::apps(
            Expr::const_(Name::from_string("NNVerify.farkasCertificateValid"), vec![]),
            [rows.clone(), r0.clone()],
        );
        let cert_ty = tc
            .infer_type(&cert)
            .expect("farkasCertificateValid <concrete> should type-check");
        assert!(
            tc.is_def_eq(&cert_ty, &Expr::sort(Level::zero())),
            "farkasCertificateValid <concrete> : Prop"
        );

        // Partially apply theorem to rows + bound: result expects the cert hyp.
        let thm = Expr::const_(
            Name::from_string("NNVerify.farkas_to_interval_constructive"),
            vec![],
        );
        let applied = Expr::apps(thm, [rows, r0]);
        let applied_ty = tc
            .infer_type(&applied)
            .expect("applied theorem should type-check");
        assert!(
            matches!(applied_ty.kind(), ExprKind::Pi(..)),
            "applied theorem should still expect the certificate hypothesis"
        );
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_farkas_to_interval_constructive()
            .expect("first");
        env.init_nn_verify_farkas_to_interval_constructive()
            .expect("second");
    }

    /// Walk an expression looking for a `Const` with the given name.
    fn mentions_const(e: &Expr, target: &str) -> bool {
        let target_name = Name::from_string(target);
        let mut stack = vec![e.clone()];
        while let Some(cur) = stack.pop() {
            match cur.kind() {
                ExprKind::Const(n, _) if *n == target_name => {
                    return true;
                }
                ExprKind::App(f, a) => {
                    stack.push((**f).clone());
                    stack.push((**a).clone());
                }
                ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                    stack.push((**ty).clone());
                    stack.push((**body).clone());
                }
                ExprKind::Let(_, ty, val, body, _) => {
                    stack.push((**ty).clone());
                    stack.push((**val).clone());
                    stack.push((**body).clone());
                }
                ExprKind::Proj(_, _, inner) => {
                    stack.push((**inner).clone());
                }
                _ => {}
            }
        }
        false
    }
}
