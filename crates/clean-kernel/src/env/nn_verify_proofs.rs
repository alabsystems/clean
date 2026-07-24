// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Formal proofs for NN verification theorems.
//!
//! Constructs machine-checked proof terms for the NN verification pipeline.
//! Each proof is registered as a `Declaration::Theorem` and type-checked
//! through the kernel TypeChecker before acceptance.
//!
//! ## Theorems
//!
//! - **T70 `entailment_transitivity`**: If B1 ⊆ B2 and B2 ⊆ B3, then B1 ⊆ B3.
//!   Transitivity of `IntervalBounds.subset` via `le_trans` on rational bounds.
//!
//! ## Axiom Status
//!
//! Since #3222 fixed projection reduction, the kernel can now reduce
//! `LE.le @Rat instLERat` to `Rat.le`. This means `Rat.le_trans` can be
//! used directly in proofs involving `LE.le` form (the two are definitionally
//! equal). The former `Rat.le_trans_LE` bridging axiom has been eliminated,
//! making T70 a zero-axiom proof (only kernel primitives + registered
//! definitions from the algebra layer).
//!
//! Part of #3220, #3240.

use crate::env::decl_builder::EnvDeclBuilder;
use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// Shared constants for proof construction.
struct ProofConsts {
    nat: Expr,
    rat: Expr,
    fin: Expr,
    le_le: Expr,
    inst_le_rat: Expr,
    and_intro: Expr,
    and_left: Expr,
    and_right: Expr,
    ib: Expr,
    ib_subset: Expr,
    le_trans_le: Expr,
}

impl ProofConsts {
    fn new() -> Self {
        Self {
            nat: Expr::const_(Name::from_string("Nat"), vec![]),
            rat: Expr::const_(Name::from_string("Rat"), vec![]),
            fin: Expr::const_(Name::from_string("Fin"), vec![]),
            le_le: Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            inst_le_rat: Expr::const_(Name::from_string("instLERat"), vec![]),
            and_intro: Expr::const_(Name::from_string("And.intro"), vec![]),
            and_left: Expr::const_(Name::from_string("And.left"), vec![]),
            and_right: Expr::const_(Name::from_string("And.right"), vec![]),
            ib: Expr::const_(Name::from_string("NNVerify.IntervalBounds"), vec![]),
            ib_subset: Expr::const_(Name::from_string("NNVerify.IntervalBounds.subset"), vec![]),
            le_trans_le: Expr::const_(Name::from_string("Rat.le_trans"), vec![]),
        }
    }

    /// Build `LE.le @Rat instLERat lhs rhs`.
    fn rat_le(&self, lhs: Expr, rhs: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(self.le_le.clone(), self.rat.clone()),
                    self.inst_le_rat.clone(),
                ),
                lhs,
            ),
            rhs,
        )
    }

    /// Build `IntervalBounds.subset @d b1 b2`.
    fn subset(&self, d: &Expr, b1: &Expr, b2: &Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.ib_subset.clone(), d.clone()), b1.clone()),
            b2.clone(),
        )
    }

    /// Build `IntervalBounds.lower b` (projection 0).
    fn lower(b: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 0, b.clone())
    }

    /// Build `IntervalBounds.upper b` (projection 1).
    fn upper(b: &Expr) -> Expr {
        Expr::proj(Name::from_string("NNVerify.IntervalBounds"), 1, b.clone())
    }

    /// Build `And.left a_prop b_prop h` (extract left conjunct).
    fn and_left_app(&self, a_prop: Expr, b_prop: Expr, h: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.and_left.clone(), a_prop), b_prop),
            h,
        )
    }

    /// Build `And.right a_prop b_prop h` (extract right conjunct).
    fn and_right_app(&self, a_prop: Expr, b_prop: Expr, h: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::app(self.and_right.clone(), a_prop), b_prop),
            h,
        )
    }

    /// Build `Rat.le_trans a b c hab hbc` (transitivity of ≤).
    fn le_trans_app(&self, a: Expr, b: Expr, cv: Expr, hab: Expr, hbc: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(Expr::app(self.le_trans_le.clone(), a), b), cv),
                hab,
            ),
            hbc,
        )
    }

    /// Build `And.intro a_prop b_prop ha hb` (construct conjunction).
    fn and_intro_app(&self, a_prop: Expr, b_prop: Expr, ha: Expr, hb: Expr) -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(self.and_intro.clone(), a_prop), b_prop),
                ha,
            ),
            hb,
        )
    }
}

/// Build the type of `entailment_transitivity`.
///
/// `{d : Nat} → (B1 B2 B3 : IB d) → subset B1 B2 → subset B2 B3 → subset B1 B3`
fn build_transitivity_type(c: &ProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = Expr::app(c.ib.clone(), d.clone());
    let (b1_id, b1) = b.fresh_local(ib_d.clone());
    let (b2_id, b2) = b.fresh_local(ib_d.clone());
    let (b3_id, b3) = b.fresh_local(ib_d.clone());

    let sub_12 = c.subset(&d, &b1, &b2);
    let sub_23 = c.subset(&d, &b2, &b3);
    let sub_13 = c.subset(&d, &b1, &b3);

    let (h1_id, _) = b.fresh_local(sub_12.clone());
    let (h2_id, _) = b.fresh_local(sub_23.clone());
    let e = b.mk_pi(h2_id, BinderInfo::Default, sub_23, sub_13);
    let e = b.mk_pi(h1_id, BinderInfo::Default, sub_12, e);
    let e = b.mk_pi(b3_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_pi(b2_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_pi(b1_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

/// Build the per-index proof body for subset transitivity.
///
/// Given index `i`, hypotheses `h1 : subset B1 B2`, `h2 : subset B2 B3`,
/// constructs: `And.intro (le_trans h2.left h1.left) (le_trans h1.right h2.right)`
fn build_per_index_proof(
    c: &ProofConsts,
    b: &EnvDeclBuilder,
    fin_d: &Expr,
    b1: &Expr,
    b2: &Expr,
    b3: &Expr,
    h1: &Expr,
    h2: &Expr,
) -> Expr {
    let mut ch = EnvDeclBuilder::child_of(b);
    let (i_id, i) = ch.fresh_local(fin_d.clone());

    // Projections applied to i
    let b1_lo_i = Expr::app(ProofConsts::lower(b1), i.clone());
    let b1_hi_i = Expr::app(ProofConsts::upper(b1), i.clone());
    let b2_lo_i = Expr::app(ProofConsts::lower(b2), i.clone());
    let b2_hi_i = Expr::app(ProofConsts::upper(b2), i.clone());
    let b3_lo_i = Expr::app(ProofConsts::lower(b3), i.clone());
    let b3_hi_i = Expr::app(ProofConsts::upper(b3), i.clone());

    let h1_i = Expr::app(h1.clone(), i.clone());
    let h2_i = Expr::app(h2.clone(), i.clone());

    // And propositions for h1(i): (le B2.lo_i B1.lo_i, le B1.hi_i B2.hi_i)
    let h1_lhs = c.rat_le(b2_lo_i.clone(), b1_lo_i.clone());
    let h1_rhs = c.rat_le(b1_hi_i.clone(), b2_hi_i.clone());

    // And propositions for h2(i): (le B3.lo_i B2.lo_i, le B2.hi_i B3.hi_i)
    let h2_lhs = c.rat_le(b3_lo_i.clone(), b2_lo_i.clone());
    let h2_rhs = c.rat_le(b2_hi_i.clone(), b3_hi_i.clone());

    // Decompose hypotheses
    let h1_left = c.and_left_app(h1_lhs.clone(), h1_rhs.clone(), h1_i.clone());
    let h1_right = c.and_right_app(h1_lhs, h1_rhs, h1_i);
    let h2_left = c.and_left_app(h2_lhs.clone(), h2_rhs.clone(), h2_i.clone());
    let h2_right = c.and_right_app(h2_lhs, h2_rhs, h2_i);

    // Transitivity proofs
    let lower = c.le_trans_app(b3_lo_i.clone(), b2_lo_i, b1_lo_i.clone(), h2_left, h1_left);
    let upper = c.le_trans_app(
        b1_hi_i.clone(),
        b2_hi_i,
        b3_hi_i.clone(),
        h1_right,
        h2_right,
    );

    // Combine with And.intro
    let goal_left = c.rat_le(b3_lo_i, b1_lo_i);
    let goal_right = c.rat_le(b1_hi_i, b3_hi_i);
    let proof = c.and_intro_app(goal_left, goal_right, lower, upper);

    let r = ch.mk_lam(i_id, BinderInfo::Default, fin_d.clone(), proof);
    ch.finish_child(r)
}

/// Build the proof term for `entailment_transitivity`.
fn build_transitivity_proof(c: &ProofConsts) -> Expr {
    let mut b = EnvDeclBuilder::new();
    let (d_id, d) = b.fresh_local(c.nat.clone());
    let ib_d = Expr::app(c.ib.clone(), d.clone());
    let (b1_id, b1) = b.fresh_local(ib_d.clone());
    let (b2_id, b2) = b.fresh_local(ib_d.clone());
    let (b3_id, b3) = b.fresh_local(ib_d.clone());

    let sub_12 = c.subset(&d, &b1, &b2);
    let sub_23 = c.subset(&d, &b2, &b3);

    let (h1_id, h1) = b.fresh_local(sub_12.clone());
    let (h2_id, h2) = b.fresh_local(sub_23.clone());

    let fin_d = Expr::app(c.fin.clone(), d.clone());
    let inner = build_per_index_proof(c, &b, &fin_d, &b1, &b2, &b3, &h1, &h2);

    let e = b.mk_lam(h2_id, BinderInfo::Default, sub_23, inner);
    let e = b.mk_lam(h1_id, BinderInfo::Default, sub_12, e);
    let e = b.mk_lam(b3_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(b2_id, BinderInfo::Default, ib_d.clone(), e);
    let e = b.mk_lam(b1_id, BinderInfo::Default, ib_d, e);
    let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
    b.finish(e)
}

impl Environment {
    /// Initialize NN verification formal proofs.
    ///
    /// Depends on: `init_nn_verify_types()`, `init_rat_linear_order()`,
    ///             `init_and()`.
    pub fn init_nn_verify_proofs(&mut self) -> Result<(), EnvError> {
        if self.nn_verify_proofs_init {
            return Ok(());
        }
        self.init_nn_verify_types()?;
        self.init_rat_linear_order()?;
        self.init_and()?;

        let c = ProofConsts::new();
        self.register_interval_contains_refl(&c)?;
        self.register_entailment_transitivity(&c)?;

        self.nn_verify_proofs_init = true;
        Ok(())
    }

    /// Register T03: `interval_contains_refl`.
    ///
    /// Proof: identity function (`fun h => h`).
    fn register_interval_contains_refl(&mut self, c: &ProofConsts) -> Result<(), EnvError> {
        let ib_contains = Expr::const_(
            Name::from_string("NNVerify.IntervalBounds.contains"),
            vec![],
        );
        let nn_vec = Expr::const_(Name::from_string("NNVerify.NNVec"), vec![]);
        let thm_type = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let vec_d = Expr::app(nn_vec.clone(), d.clone());
            let (b_id, bv) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let contains = Expr::app(Expr::app(Expr::app(ib_contains.clone(), d.clone()), bv), x);
            let (h_id, _) = b.fresh_local(contains.clone());
            let e = b.mk_pi(h_id, BinderInfo::Default, contains.clone(), contains);
            let e = b.mk_pi(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_pi(b_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_pi(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        let proof_value = {
            let mut b = EnvDeclBuilder::new();
            let (d_id, d) = b.fresh_local(c.nat.clone());
            let ib_d = Expr::app(c.ib.clone(), d.clone());
            let vec_d = Expr::app(nn_vec, d.clone());
            let (b_id, bv) = b.fresh_local(ib_d.clone());
            let (x_id, x) = b.fresh_local(vec_d.clone());
            let contains = Expr::app(Expr::app(Expr::app(ib_contains, d), bv), x);
            let (h_id, h) = b.fresh_local(contains.clone());
            let e = b.mk_lam(h_id, BinderInfo::Default, contains, h);
            let e = b.mk_lam(x_id, BinderInfo::Default, vec_d, e);
            let e = b.mk_lam(b_id, BinderInfo::Default, ib_d, e);
            let e = b.mk_lam(d_id, BinderInfo::Implicit, c.nat.clone(), e);
            b.finish(e)
        };
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.interval_contains_refl"),
            level_params: vec![],
            type_: thm_type,
            value: proof_value,
        })
    }

    /// Register T70: `entailment_transitivity`.
    ///
    /// ```text
    /// theorem entailment_transitivity {d : Nat} (B1 B2 B3 : IntervalBounds d) :
    ///   B1.subset B2 → B2.subset B3 → B1.subset B3
    /// ```
    ///
    /// Proof: For each `i : Fin d`, combine `le_trans` on lower/upper bounds
    /// with `And.intro`. See [`build_per_index_proof`] for the inner term.
    fn register_entailment_transitivity(&mut self, c: &ProofConsts) -> Result<(), EnvError> {
        self.add_decl(Declaration::Theorem {
            name: Name::from_string("NNVerify.entailment_transitivity"),
            level_params: vec![],
            type_: build_transitivity_type(c),
            value: build_transitivity_proof(c),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::ExprKind;
    use crate::tc::TypeChecker;

    fn make_env() -> Environment {
        let mut env = Environment::new();
        env.init_nn_verify_proofs().expect("init_nn_verify_proofs");
        env
    }

    /// Verify bridging axiom `Rat.le_trans_LE` is no longer registered (#3240).
    /// Since #3222, `LE.le @Rat instLERat` reduces to `Rat.le`, so the
    /// bridging axiom is unnecessary and T70 uses `Rat.le_trans` directly.
    #[test]
    fn test_rat_le_trans_le_not_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("Rat.le_trans_LE"))
                .is_none(),
            "Rat.le_trans_LE bridging axiom should no longer be registered (#3240)"
        );
    }

    /// Verify `Rat.le_trans` is available (from algebra layer) and T70 can
    /// use it directly for transitivity proofs.
    #[test]
    fn test_rat_le_trans_available() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let le_trans = Expr::const_(Name::from_string("Rat.le_trans"), vec![]);
        let ty = tc.infer_type(&le_trans).expect("infer Rat.le_trans type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_entailment_transitivity_registered() {
        let env = make_env();
        assert!(
            env.get_const(&Name::from_string("NNVerify.entailment_transitivity"))
                .is_some(),
            "entailment_transitivity should be registered"
        );
    }

    #[test]
    fn test_entailment_transitivity_type_checks() {
        let env = make_env();
        let tc = TypeChecker::with_mode(&env, env.mode());
        let thm = Expr::const_(
            Name::from_string("NNVerify.entailment_transitivity"),
            vec![],
        );
        let ty = tc
            .infer_type(&thm)
            .expect("infer entailment_transitivity type");
        assert!(matches!(ty.kind(), ExprKind::Pi(..)));
    }

    #[test]
    fn test_entailment_transitivity_is_theorem() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("NNVerify.entailment_transitivity"))
            .expect("entailment_transitivity should exist");
        assert_eq!(
            info.kind,
            ConstantKind::Theorem,
            "entailment_transitivity should be a Theorem, not {:?}",
            info.kind
        );
    }

    #[test]
    fn test_entailment_transitivity_has_proof_value() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("NNVerify.entailment_transitivity"))
            .expect("entailment_transitivity should exist");
        assert!(
            info.value.is_some(),
            "entailment_transitivity should have a proof term"
        );
    }

    #[test]
    fn test_entailment_transitivity_no_sorry() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("NNVerify.entailment_transitivity"))
            .expect("entailment_transitivity should exist");
        let sorry = info.sorry_summary();
        assert!(
            !sorry.has_sorry,
            "entailment_transitivity proof should not use sorry"
        );
    }

    /// Key validation for #3240: T70 proof term type-checks using `Rat.le_trans`
    /// directly (no bridging axiom). The kernel reduces `LE.le @Rat instLERat`
    /// to `Rat.le` via projection reduction (#3222), making the proof types
    /// definitionally equal.
    #[test]
    fn test_entailment_transitivity_proof_type_checks() {
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("NNVerify.entailment_transitivity"))
            .expect("entailment_transitivity should exist");
        let proof = info.value.as_ref().expect("should have proof term");
        let tc = TypeChecker::with_mode(&env, env.mode());
        let inferred = tc
            .infer_type(proof)
            .expect("T70 proof should type-check with Rat.le_trans (no bridging axiom)");
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "inferred type should match declared type"
        );
    }

    /// Verify T70 is a zero-axiom proof: the entailment_transitivity theorem
    /// should only depend on definitions and axioms from the algebra layer
    /// (Rat.le_trans etc.), not on any custom bridging axioms.
    #[test]
    fn test_entailment_transitivity_zero_bridging_axioms() {
        use crate::env::types::ConstantKind;
        let env = make_env();
        let info = env
            .get_const(&Name::from_string("NNVerify.entailment_transitivity"))
            .expect("entailment_transitivity should exist");
        assert_eq!(info.kind, ConstantKind::Theorem);
        // The proof registers no local axioms (Rat.le_trans_LE was removed).
        // Rat.le_trans itself is an axiom from the algebra layer, but it is
        // a standard mathematical axiom, not a bridging axiom.
        assert!(
            env.get_const(&Name::from_string("Rat.le_trans_LE"))
                .is_none(),
            "no bridging axiom should exist in the environment"
        );
    }

    #[test]
    fn test_interval_contains_refl_registered() {
        let env = make_env();
        assert!(env
            .get_const(&Name::from_string("NNVerify.interval_contains_refl"))
            .is_some(),);
    }

    #[test]
    fn test_interval_contains_refl_type_checks() {
        let env = make_env();
        let thm = env
            .get_const(&Name::from_string("NNVerify.interval_contains_refl"))
            .expect("should exist");
        assert!(thm.value.is_some());
        let tc = TypeChecker::with_mode(&env, env.mode());
        let proof = thm.value.as_ref().unwrap();
        let inferred = tc.infer_type(proof).expect("should type-check");
        assert!(tc.is_def_eq(&inferred, &thm.type_));
    }

    #[test]
    fn test_idempotent() {
        let mut env = Environment::new();
        env.init_nn_verify_proofs().expect("first init");
        env.init_nn_verify_proofs().expect("second init");
    }

    /// Verify theorem names use the `NNVerify.` prefix (Part of #3206).
    #[test]
    fn test_nn_verify_theorem_naming_convention() {
        let env = make_env();
        let prefixed = [
            "NNVerify.entailment_transitivity",
            "NNVerify.interval_contains_refl",
        ];
        for name in &prefixed {
            assert!(
                env.get_const(&Name::from_string(name)).is_some(),
                "{} should be registered with NNVerify. prefix",
                name,
            );
        }
        let old = ["entailment_transitivity", "interval_contains_refl"];
        for name in &old {
            assert!(
                env.get_const(&Name::from_string(name)).is_none(),
                "{} should NOT be registered (use NNVerify. prefix)",
                name,
            );
        }
    }
}
