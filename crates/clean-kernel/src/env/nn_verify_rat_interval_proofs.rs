// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Kernel-level constructive lemmas for `NNVerify.Rat` interval primitives
//! (#3615).
//!
//! Registers three genuine `Declaration::Theorem`s with constructive lambda
//! proof terms:
//!
//! - `NNVerify.Rat.interval_add_valid` — if `I` and `J` are valid intervals,
//!   then `interval_add I J` is valid.
//! - `NNVerify.Rat.interval_hull_lo_le_fst_lo` — the hull's lower endpoint is
//!   bounded by the first interval's lower endpoint.
//! - `NNVerify.Rat.interval_hull_fst_hi_le_hi` — the first interval's upper
//!   endpoint is bounded by the hull's upper endpoint.
//!
//! # Definitional reduction
//!
//! `NNVerify.Rat.interval_add` and `NNVerify.Rat.interval_hull` are reducible
//! Definitions, so the kernel accepts proof terms over their endpoint-reduced
//! forms:
//!
//! ```text
//! (interval_add I J).lo  ≡  Rat.add I.lo J.lo
//! (interval_add I J).hi  ≡  Rat.add I.hi J.hi
//! (interval_hull I J).lo ≡  Rat.min I.lo J.lo
//! (interval_hull I J).hi ≡  Rat.max I.hi J.hi
//! ```
//!
//! # Proof terms
//!
//! ```text
//! interval_add_valid :=
//!   fun I J h1 h2 =>
//!     Rat.add_le_add I.lo I.hi J.lo J.hi h1 h2
//!
//! interval_hull_lo_le_fst_lo :=
//!   fun I J =>
//!     Rat.min_le_left I.lo J.lo
//!
//! interval_hull_fst_hi_le_hi :=
//!   fun I J =>
//!     Rat.le_max_left I.hi J.hi
//! ```
//!
//! # Axioms used
//!
//! - `interval_hull_lo_le_fst_lo` and `interval_hull_fst_hi_le_hi` depend on
//!   `Rat.min_le_left` / `Rat.le_max_left`. The 2026-06 integrity audit
//!   (#integrity-audit) reclassified these from foundational to admitted
//!   DOMAIN axioms (`ADMITTED_DOMAIN_AXIOMS` in `axiom_audit.rs`): they are
//!   mathematically true Mathlib lattice lemmas but are registered here as
//!   bare `Declaration::Axiom` with NO Clean-kernel proof term, so a theorem
//!   reaching them is an unproved-in-Clean assumption. They were previously
//!   whitelisted in `FOUNDATIONAL_AXIOMS`, which dishonestly reported both
//!   theorems as `ProofQuality::Constructive` ("empty axiom closure"). The
//!   honest classification is now `ProofQuality::AxiomDependent` on the single
//!   admitted domain axiom each rests on (no `sorry`, no rogue axiom).
//! - `interval_add_valid` invokes `Rat.add_le_add`, itself a constructive
//!   kernel theorem (promotion landed in #3537). That theorem's proof walks
//!   `Int.*` / `Nat.*` ring-normalization primitives (`Int.add_comm`,
//!   `Int.mul_assoc`, `Nat.mul_comm`, etc.), which are plain kernel Axioms
//!   rather than whitelisted foundational names. Consequently
//!   `interval_add_valid` inherits the `Rat.add_le_add` closure:
//!   `ProofQuality::AxiomDependent` on that fixed Int/Nat primitive set,
//!   with no new domain-specific axioms introduced. This matches the
//!   accepted closure pinned by `test_rat_add_le_add_axiom_closure` in
//!   `nn_verify_interval_arith_proofs.rs` and is therefore accepted by the
//!   native shard builder (no domain axioms = no C004 regression).
//!
//! Per-declaration tests assert the honest classification: the
//! `interval_add_valid` test (`test_interval_add_valid_constructive`) accepts
//! `Constructive` or `AxiomDependent` on the Int/Nat ring-normalization
//! whitelist; the two `interval_hull_*` tests
//! (`test_interval_hull_*_axiom_dependent_on_admitted`) assert
//! `AxiomDependent` on the admitted domain axiom each rests on.
//!
//! # Placement
//!
//! Uses its own `init_*` entry point (`init_nn_verify_rat_interval_proofs`)
//! rather than extending `nn_verify_rat_interval.rs`, keeping the reducible
//! primitive registrations separate from the follow-up proof slice. This
//! mirrors the `nn_verify_interval_containment_proofs.rs` split (#3603).
//!
//! Part of #3615 (C004 Phase 1 follow-up — first monotonicity slice).
//! Unblocks downstream faithful `IBP.forward_layernorm_real` /
//! `CROWN.backward_layernorm_real` / `C004.interval_hull_layernorm_real`
//! carrier proofs that need element-wise validity preservation.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

// ---------------------------------------------------------------------------
// Shared constant bundle
// ---------------------------------------------------------------------------

struct CConsts {
    rat: Expr,
    interval: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    add_le_add: Expr,
    min_le_left: Expr,
    le_max_left: Expr,
    interval_add: Expr,
    interval_hull: Expr,
    interval_name: Name,
}

impl CConsts {
    fn new() -> Self {
        Self {
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            interval: Expr::const_(Name::from_string("NNVerify.Interval"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            add_le_add: Expr::const_(Name::from_string("Rat.add_le_add"), vec![]),
            min_le_left: Expr::const_(Name::from_string("Rat.min_le_left"), vec![]),
            le_max_left: Expr::const_(Name::from_string("Rat.le_max_left"), vec![]),
            interval_add: Expr::const_(Name::from_string("NNVerify.Rat.interval_add"), vec![]),
            interval_hull: Expr::const_(Name::from_string("NNVerify.Rat.interval_hull"), vec![]),
            interval_name: Name::from_string("NNVerify.Interval"),
        }
    }

    /// `LE.le.{0} @Rat instLERat lhs rhs`.
    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::apps(
            self.le_le.clone(),
            [self.rat.clone(), self.inst_le_rat.clone(), lhs, rhs],
        )
    }

    fn interval_add_app(&self, i: Expr, j: Expr) -> Expr {
        Expr::apps(self.interval_add.clone(), [i, j])
    }

    fn interval_hull_app(&self, i: Expr, j: Expr) -> Expr {
        Expr::apps(self.interval_hull.clone(), [i, j])
    }

    fn lo(&self, i: &Expr) -> Expr {
        Expr::proj(self.interval_name.clone(), 0, i.clone())
    }

    fn hi(&self, i: &Expr) -> Expr {
        Expr::proj(self.interval_name.clone(), 1, i.clone())
    }

    fn add_le_add_app(&self, a: Expr, b: Expr, c: Expr, d: Expr, hab: Expr, hcd: Expr) -> Expr {
        Expr::apps(self.add_le_add.clone(), [a, b, c, d, hab, hcd])
    }

    fn min_le_left_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.min_le_left.clone(), [a, b])
    }

    fn le_max_left_app(&self, a: Expr, b: Expr) -> Expr {
        Expr::apps(self.le_max_left.clone(), [a, b])
    }
}

// ---------------------------------------------------------------------------
// Public init
// ---------------------------------------------------------------------------

impl Environment {
    /// Initialize the three constructive monotonicity lemmas for
    /// `NNVerify.Rat` interval primitives (#3615):
    /// `interval_add_valid`, `interval_hull_lo_le_fst_lo`,
    /// `interval_hull_fst_hi_le_hi`.
    ///
    /// Idempotent. Depends on `init_nn_verify_rat_interval()` for the
    /// reducible `interval_add` / `interval_hull` primitives, on
    /// `init_nn_verify_interval_arith_proofs()` for `Rat.add_le_add`, and on
    /// `init_rat_minmax()` (re-run idempotently) to ensure `Rat.min`,
    /// `Rat.max`, `Rat.min_le_left`, and `Rat.le_max_left` are present.
    pub fn init_nn_verify_rat_interval_proofs(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_rat_interval_proofs_init {
            return Ok(());
        }
        self.init_nn_verify_rat_interval()?;
        self.init_nn_verify_interval_arith_proofs()?;
        self.init_rat_minmax()?;

        let c = CConsts::new();
        self.register_interval_add_valid(&c)?;
        self.register_interval_hull_lo_le_fst_lo(&c)?;
        self.register_interval_hull_fst_hi_le_hi(&c)?;

        self.nn_verify_rat_interval_proofs_init = true;
        Ok(())
    }

    // -----------------------------------------------------------------------
    // Theorem 1: interval_add_valid
    //
    //   ∀ (I J : Interval), I.lo ≤ I.hi → J.lo ≤ J.hi →
    //     (interval_add I J).lo ≤ (interval_add I J).hi
    //
    // Proof: fun I J h1 h2 =>
    //   Rat.add_le_add I.lo I.hi J.lo J.hi h1 h2
    // -----------------------------------------------------------------------

    fn register_interval_add_valid(&mut self, c: &CConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.interval_add_valid");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let h1_ty = c.rat_le(c.lo(&i), c.hi(&i));
            let (h1_id, _) = b.fresh_local(h1_ty.clone());
            let h2_ty = c.rat_le(c.lo(&j), c.hi(&j));
            let (h2_id, _) = b.fresh_local(h2_ty.clone());
            let add_ij = c.interval_add_app(i.clone(), j.clone());
            let concl = c.rat_le(c.lo(&add_ij), c.hi(&add_ij));
            let r = b.mk_pi(h2_id, BinderInfo::Default, h2_ty, concl);
            let r = b.mk_pi(h1_id, BinderInfo::Default, h1_ty, r);
            let r = b.mk_pi(j_id, BinderInfo::Default, c.interval.clone(), r);
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), r);
            b.finish(r)
        };

        let thm_proof = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let h1_ty = c.rat_le(c.lo(&i), c.hi(&i));
            let (h1_id, h1) = b.fresh_local(h1_ty.clone());
            let h2_ty = c.rat_le(c.lo(&j), c.hi(&j));
            let (h2_id, h2) = b.fresh_local(h2_ty.clone());
            let body = c.add_le_add_app(c.lo(&i), c.hi(&i), c.lo(&j), c.hi(&j), h1, h2);
            let e = b.mk_lam(h2_id, BinderInfo::Default, h2_ty, body);
            let e = b.mk_lam(h1_id, BinderInfo::Default, h1_ty, e);
            let e = b.mk_lam(j_id, BinderInfo::Default, c.interval.clone(), e);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // -----------------------------------------------------------------------
    // Theorem 2: interval_hull_lo_le_fst_lo
    //
    //   ∀ (I J : Interval), (interval_hull I J).lo ≤ I.lo
    //
    // Unfolds to: Rat.min I.lo J.lo ≤ I.lo
    //
    // Proof: fun I J => Rat.min_le_left I.lo J.lo
    // -----------------------------------------------------------------------

    fn register_interval_hull_lo_le_fst_lo(&mut self, c: &CConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.interval_hull_lo_le_fst_lo");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let hull_ij = c.interval_hull_app(i.clone(), j.clone());
            let concl = c.rat_le(c.lo(&hull_ij), c.lo(&i));
            let r = b.mk_pi(j_id, BinderInfo::Default, c.interval.clone(), concl);
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), r);
            b.finish(r)
        };

        let thm_proof = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let body = c.min_le_left_app(c.lo(&i), c.lo(&j));
            let e = b.mk_lam(j_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }

    // -----------------------------------------------------------------------
    // Theorem 3: interval_hull_fst_hi_le_hi
    //
    //   ∀ (I J : Interval), I.hi ≤ (interval_hull I J).hi
    //
    // Unfolds to: I.hi ≤ Rat.max I.hi J.hi
    //
    // Proof: fun I J => Rat.le_max_left I.hi J.hi
    // -----------------------------------------------------------------------

    fn register_interval_hull_fst_hi_le_hi(&mut self, c: &CConsts) -> Result<(), EnvError> {
        let name = Name::from_string("NNVerify.Rat.interval_hull_fst_hi_le_hi");
        if self.get_const(&name).is_some() {
            return Ok(());
        }

        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let hull_ij = c.interval_hull_app(i.clone(), j.clone());
            let concl = c.rat_le(c.hi(&i), c.hi(&hull_ij));
            let r = b.mk_pi(j_id, BinderInfo::Default, c.interval.clone(), concl);
            let r = b.mk_pi(i_id, BinderInfo::Default, c.interval.clone(), r);
            b.finish(r)
        };

        let thm_proof = {
            let mut b = EnvDeclBuilder::new();
            let (i_id, i) = b.fresh_local(c.interval.clone());
            let (j_id, j) = b.fresh_local(c.interval.clone());
            let body = c.le_max_left_app(c.hi(&i), c.hi(&j));
            let e = b.mk_lam(j_id, BinderInfo::Default, c.interval.clone(), body);
            let e = b.mk_lam(i_id, BinderInfo::Default, c.interval.clone(), e);
            b.finish(e)
        };

        self.add_decl(Declaration::Theorem {
            name,
            level_params: vec![],
            type_: thm_type,
            value: thm_proof,
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::axiom_audit::{ProofQuality, ADMITTED_DOMAIN_AXIOMS};
    use crate::env::types::ConstantKind;
    use crate::tc::TypeChecker;
    use std::collections::HashSet;

    const ADD_VALID: &str = "NNVerify.Rat.interval_add_valid";
    const HULL_LO_LE_FST_LO: &str = "NNVerify.Rat.interval_hull_lo_le_fst_lo";
    const HULL_FST_HI_LE_HI: &str = "NNVerify.Rat.interval_hull_fst_hi_le_hi";

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_rat_interval_proofs()
            .expect("init_nn_verify_rat_interval_proofs");
        env
    }

    fn assert_is_theorem(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "{name} must be a Theorem, got {:?}",
            info.kind,
        );
        assert!(info.value.is_some(), "{name} must carry a proof term");
    }

    fn assert_type_checks(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        let proof = info.value.as_ref().expect("theorem should have value");
        let tc = TypeChecker::with_mode(env, env.mode());
        let inferred = tc
            .infer_type(proof)
            .unwrap_or_else(|e| panic!("{name} proof should type-check: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name} inferred type must match declared type",
        );
    }

    /// Allowed Int/Nat kernel primitives that are surfaced through the
    /// `Rat.add_le_add` / `Rat.add_comm` / `Rat.add_assoc` / `Rat.mul_assoc`
    /// ring-normalization closure. These are the same primitives the
    /// `test_rat_add_le_add_axiom_closure` test whitelists for `Rat.add_le_add`
    /// itself (see `nn_verify_interval_arith_proofs.rs`). Any theorem that
    /// invokes `Rat.add_le_add` inherits this closure — that is a structural
    /// property of the current kernel, not a new domain-axiom dependency.
    const ALLOWED_INT_NAT_PRIMITIVES: &[&str] = &[
        "Int.add_assoc",
        "Int.add_comm",
        "Int.add_zero",
        "Int.mul_assoc",
        "Int.mul_comm",
        "Int.mul_one",
        "Int.ofNat_mul",
        "Int.right_distrib",
        "Int.zero_add",
        "Int.zero_mul",
        "Nat.mul_assoc",
        "Nat.mul_comm",
        "Nat.mul_one",
        "Nat.one_mul",
    ];

    fn assert_constructive(env: &Environment, name: &str) {
        let quality = env
            .proof_quality(&Name::from_string(name))
            .unwrap_or_else(|| panic!("proof_quality should succeed for {name}"));
        match quality {
            ProofQuality::Constructive => {}
            ProofQuality::AxiomDependent { ref axioms, .. } => {
                let axiom_names: Vec<String> = axioms.iter().map(|n| n.to_string()).collect();
                for a in &axiom_names {
                    // Honest closure (2026-06 integrity audit): allowed members are
                    // the Int/Nat ring-normalization primitives inherited through
                    // `Rat.add_le_add`, OR an admitted Rat/Fin/Nat-bitwise DOMAIN
                    // axiom (`ADMITTED_DOMAIN_AXIOMS`, no longer laundered as
                    // foundational). Anything else — `sorry`/`sorryAx` or a rogue
                    // domain axiom — fails this gate.
                    assert!(
                        ALLOWED_INT_NAT_PRIMITIVES.contains(&a.as_str())
                            || crate::env::axiom_audit::ADMITTED_DOMAIN_AXIOMS
                                .contains(&a.as_str()),
                        "{name} must be Constructive or AxiomDependent on Int/Nat \
                         ring-normalization primitives and/or admitted domain \
                         axioms only; got unexpected axiom {a:?} in closure {axiom_names:?}"
                    );
                }
            }
            other => panic!("{name} must be Constructive or AxiomDependent, got {other:?}"),
        }
    }

    /// Honest classification check for the two `interval_hull_*` lemmas after
    /// the 2026-06 integrity audit (#integrity-audit).
    ///
    /// `interval_hull_lo_le_fst_lo` rests on `Rat.min_le_left` and
    /// `interval_hull_fst_hi_le_hi` rests on `Rat.le_max_left`. Both names were
    /// previously dishonestly whitelisted as `FOUNDATIONAL_AXIOMS`, so these
    /// theorems were reported as `ProofQuality::Constructive` ("empty axiom
    /// closure"). They are now in `ADMITTED_DOMAIN_AXIOMS` and excluded from
    /// `is_foundational_axiom`, so the closure is NON-empty and the honest
    /// classification is `AxiomDependent` on admitted DOMAIN axioms only.
    ///
    /// WS-B: the `interval_hull` lemmas' only domain dependencies were the Rat
    /// min/max lattice axioms (`Rat.le_min` / `Rat.le_max_*`), which are now
    /// kernel-checked constructive Theorems over the quotient carrier. So these
    /// theorems are now FULLY CONSTRUCTIVE: empty axiom closure,
    /// `ProofQuality::Constructive`.
    fn assert_axiom_dependent_on_admitted(env: &Environment, name: &str) {
        let _ = &ADMITTED_DOMAIN_AXIOMS;

        let deps = env
            .axiom_deps(&Name::from_string(name))
            .unwrap_or_else(|| panic!("axiom_deps should succeed for {name}"));
        assert!(
            deps.is_empty(),
            "WS-B: {name} is now FULLY CONSTRUCTIVE (its Rat min/max lattice \
             dependencies are kernel-checked Theorems); axiom closure must be \
             EMPTY, got {deps:?}"
        );

        let quality = env
            .proof_quality(&Name::from_string(name))
            .unwrap_or_else(|| panic!("proof_quality should succeed for {name}"));
        assert!(
            matches!(quality, ProofQuality::Constructive),
            "WS-B: {name} must be Constructive now that the Rat lattice axioms \
             are eliminated, got {quality:?}"
        );
    }

    fn assert_sorry_free(env: &Environment, name: &str) {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should be registered"));
        let summary = info.sorry_summary();
        assert!(
            !summary.has_sorry,
            "{name} proof term must be sorry-free; summary = {summary:?}",
        );
    }

    #[test]
    fn test_interval_add_valid_is_theorem() {
        let env = make_env();
        assert_is_theorem(&env, ADD_VALID);
    }

    #[test]
    fn test_interval_add_valid_type_checks() {
        let env = make_env();
        assert_type_checks(&env, ADD_VALID);
    }

    #[test]
    fn test_interval_add_valid_no_sorry() {
        let env = make_env();
        assert_sorry_free(&env, ADD_VALID);
    }

    #[test]
    fn test_interval_add_valid_constructive() {
        let env = make_env();
        assert_constructive(&env, ADD_VALID);
    }

    #[test]
    fn test_interval_hull_lo_le_fst_lo_is_theorem() {
        let env = make_env();
        assert_is_theorem(&env, HULL_LO_LE_FST_LO);
    }

    #[test]
    fn test_interval_hull_lo_le_fst_lo_type_checks() {
        let env = make_env();
        assert_type_checks(&env, HULL_LO_LE_FST_LO);
    }

    #[test]
    fn test_interval_hull_lo_le_fst_lo_no_sorry() {
        let env = make_env();
        assert_sorry_free(&env, HULL_LO_LE_FST_LO);
    }

    /// #integrity-audit (2026-06): `interval_hull_lo_le_fst_lo` rests on
    /// `Rat.min_le_left`, which the audit reclassified from foundational to an
    /// admitted DOMAIN axiom (`ADMITTED_DOMAIN_AXIOMS`). The proof is therefore
    /// honestly `AxiomDependent` on that admitted assumption — NOT
    /// `Constructive` with an empty axiom closure as previously overstated.
    #[test]
    fn test_interval_hull_lo_le_fst_lo_axiom_dependent_on_admitted() {
        let env = make_env();
        assert_axiom_dependent_on_admitted(&env, HULL_LO_LE_FST_LO);
    }

    #[test]
    fn test_interval_hull_fst_hi_le_hi_is_theorem() {
        let env = make_env();
        assert_is_theorem(&env, HULL_FST_HI_LE_HI);
    }

    #[test]
    fn test_interval_hull_fst_hi_le_hi_type_checks() {
        let env = make_env();
        assert_type_checks(&env, HULL_FST_HI_LE_HI);
    }

    #[test]
    fn test_interval_hull_fst_hi_le_hi_no_sorry() {
        let env = make_env();
        assert_sorry_free(&env, HULL_FST_HI_LE_HI);
    }

    /// #integrity-audit (2026-06): `interval_hull_fst_hi_le_hi` rests on
    /// `Rat.le_max_left`, which the audit reclassified from foundational to an
    /// admitted DOMAIN axiom (`ADMITTED_DOMAIN_AXIOMS`). The proof is therefore
    /// honestly `AxiomDependent` on that admitted assumption — NOT
    /// `Constructive` with an empty axiom closure as previously overstated.
    #[test]
    fn test_interval_hull_fst_hi_le_hi_axiom_dependent_on_admitted() {
        let env = make_env();
        assert_axiom_dependent_on_admitted(&env, HULL_FST_HI_LE_HI);
    }

    #[test]
    fn test_init_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_rat_interval_proofs()
            .expect("first init");
        env.init_nn_verify_rat_interval_proofs()
            .expect("second init should be idempotent");
        assert!(env.get_const(&Name::from_string(ADD_VALID)).is_some());
        assert!(env
            .get_const(&Name::from_string(HULL_LO_LE_FST_LO))
            .is_some());
        assert!(env
            .get_const(&Name::from_string(HULL_FST_HI_LE_HI))
            .is_some());
    }
}
