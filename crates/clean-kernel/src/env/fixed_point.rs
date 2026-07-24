// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Fixed Point Theory for Environment
//!
//! Copyright 2026 Andrew Yates
//! Licensed under Apache-2.0
//!
//! This module provides axioms and structures for fixed point theory:
//! - Least fixed points (lfp) and greatest fixed points (gfp)
//! - Knaster-Tarski theorem (fixed points in complete lattices)
//! - Induction principle for least fixed points
//! - Coinduction principle for greatest fixed points
//!
//! These are essential for TLAPS (TLA+ Proof System) backend integration,
//! where temporal logic obligations require fixed point reasoning.
//!
//! ## References
//! - Tarski, A. (1955). A lattice-theoretical fixpoint theorem and its applications.
//! - TLAPM source: <https://github.com/tlaplus/tlapm>
//! - Issue #12: TLAPS backend requirements for TY

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;

impl Environment {
    /// Initialize Fixed Point Theory module
    ///
    /// Fixed point theory provides the foundation for reasoning about
    /// recursive definitions, temporal logic, and inductive/coinductive types.
    ///
    /// ## Key Concepts
    ///
    /// **Least Fixed Point (lfp):**
    /// Given a monotone function f : P(D) → P(D), the least fixed point is:
    ///   lfp(D, f) ≡ ∩{S ∈ SUBSET D : f(S) ⊆ S}
    ///
    /// **Greatest Fixed Point (gfp):**
    ///   gfp(D, f) ≡ ∪{S ∈ SUBSET D : S ⊆ f(S)}
    ///
    /// **Knaster-Tarski Theorem:**
    /// In a complete lattice, every monotone function has a least and greatest fixed point.
    ///
    /// ## TLA+ Integration
    ///
    /// TLA+ uses fixed points for:
    /// - Safety properties: greatest fixed point (□P - always P)
    /// - Liveness properties: least fixed point (◇P - eventually P)
    /// - Recursive operator definitions
    ///
    /// # Contract
    ///
    /// REQUIRES: `self` is a valid Environment instance
    /// ENSURES: On success, `self.fixed_point_init == true`
    /// ENSURES: On success, required dependencies (`set_theory`, `eq`) are initialized
    /// ENSURES: Idempotent - calling multiple times returns `Ok(())` without duplication
    pub fn init_fixed_point(&mut self) -> Result<(), EnvError> {
        if self.fixed_point_init {
            return Ok(());
        }

        // Dependencies: set theory for subset/powerset concepts
        self.init_set_theory()?;
        self.init_eq()?;

        let u = Name::from_string("u");
        let u_level = Level::param(u.clone());
        let type_u = Expr::sort(Level::succ(u_level.clone()));

        // ================================================================
        // Core Fixed Point Operations
        // ================================================================
        for name in &[
            // Fixed point operations
            "FixedPoint.lfp", // lfp : (D : Set) → (f : Set → Set) → Set
            "FixedPoint.gfp", // gfp : (D : Set) → (f : Set → Set) → Set
            // Monotonicity predicate (required for Knaster-Tarski)
            "FixedPoint.Monotone", // Monotone : (f : Set → Set) → Prop
            // Fixed point characterization
            "FixedPoint.IsFixedPoint", // IsFixedPoint : (f : Set → Set) → Set → Prop
            "FixedPoint.IsLeastFixedPoint", // IsLeastFixedPoint : (f : Set → Set) → Set → Prop
            "FixedPoint.IsGreatestFixedPoint", // IsGreatestFixedPoint : (f : Set → Set) → Set → Prop
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Knaster-Tarski Theorem
        // ================================================================
        for name in &[
            // Main theorem: monotone functions have fixed points
            "FixedPoint.lfp_exists", // Monotone f → ∃ x, f x = x ∧ ∀ y, f y ⊆ y → x ⊆ y
            "FixedPoint.gfp_exists", // Monotone f → ∃ x, f x = x ∧ ∀ y, y ⊆ f y → y ⊆ x
            // lfp and gfp are indeed fixed points
            "FixedPoint.lfp_is_fixed", // Monotone f → f (lfp D f) = lfp D f
            "FixedPoint.gfp_is_fixed", // Monotone f → f (gfp D f) = gfp D f
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Unfolding Principles
        // ================================================================
        for name in &[
            // lfp unfolding (allows expanding recursive definitions)
            "FixedPoint.lfp_unfold", // Monotone f → lfp D f = f (lfp D f)
            // gfp unfolding
            "FixedPoint.gfp_unfold", // Monotone f → gfp D f = f (gfp D f)
            // Rolling/unrolling for nested fixed points
            "FixedPoint.lfp_roll", // lfp D (f ∘ g) = f (lfp D (g ∘ f))
            "FixedPoint.gfp_roll", // gfp D (f ∘ g) = f (gfp D (g ∘ f))
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Induction Principles (for lfp)
        // ================================================================
        for name in &[
            // Park induction: to prove P holds for all x ∈ lfp D f,
            // show that P is preserved by f
            "FixedPoint.lfp_induction",
            // Stronger version with additional context
            "FixedPoint.lfp_strong_induction",
            // Mutual induction for simultaneous fixed points
            "FixedPoint.lfp_mutual_induction",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Coinduction Principles (for gfp)
        // ================================================================
        for name in &[
            // Coinduction: to prove x ∈ gfp D f,
            // show x is in some post-fixed point
            "FixedPoint.gfp_coinduction",
            // Bisimulation coinduction
            "FixedPoint.gfp_bisimulation",
            // Up-to techniques for efficient coinduction
            "FixedPoint.gfp_upto",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Monotonicity Lemmas
        // ================================================================
        for name in &[
            // Basic monotonicity results
            "FixedPoint.lfp_mono",   // f ⊆ g → lfp D f ⊆ lfp D g
            "FixedPoint.gfp_mono",   // f ⊆ g → gfp D f ⊆ gfp D g
            "FixedPoint.lfp_le_gfp", // Monotone f → lfp D f ⊆ gfp D f
            // Composition preserves monotonicity
            "FixedPoint.mono_comp", // Monotone f → Monotone g → Monotone (f ∘ g)
            "FixedPoint.mono_union", // Monotone (λ S. A ∪ S)
            "FixedPoint.mono_inter", // Monotone (λ S. A ∩ S)
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Lattice-Theoretic Results
        // ================================================================
        for name in &[
            // Complete lattice fixed point theorem (generalized Knaster-Tarski)
            "FixedPoint.complete_lattice_lfp",
            "FixedPoint.complete_lattice_gfp",
            // Continuous functions (preserve directed suprema)
            "FixedPoint.Continuous",     // Continuous : (Set → Set) → Prop
            "FixedPoint.continuous_lfp", // Continuous f → lfp is supremum of finite iterations
            // Iteration characterization (Kleene)
            "FixedPoint.lfp_iterate", // lfp D f = ⋃ₙ fⁿ(∅)
            "FixedPoint.gfp_iterate", // gfp D f = ⋂ₙ fⁿ(D)
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // TLA+ Specific: Temporal Fixed Points
        // ================================================================
        for name in &[
            // Next (○P): P holds in the next state
            // Required for temporal unfolding: □P = P ∧ ○(□P), ◇P = P ∨ ○(◇P)
            "FixedPoint.TLA_next",
            // Eventually (◇P): least fixed point of λS. P ∪ ○S
            "FixedPoint.TLA_eventually",
            // Always (□P): greatest fixed point of λS. P ∩ ○S
            "FixedPoint.TLA_always",
            // Leads-to (P ~> Q): □(P → ◇Q)
            "FixedPoint.TLA_leads_to",
            // Well-founded induction on leads-to chains
            "FixedPoint.TLA_wf_induction",
            // Strong fairness
            "FixedPoint.TLA_strong_fairness",
            // Weak fairness
            "FixedPoint.TLA_weak_fairness",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Temporal Unfolding Axioms (using TLA_next)
        // ================================================================
        for name in &[
            // □P = P ∧ ○(□P) - Always unfolds to current and next
            "FixedPoint.TLA_always_unfold",
            // ◇P = P ∨ ○(◇P) - Eventually unfolds to current or next
            "FixedPoint.TLA_eventually_unfold",
            // ○(□P) = □(○P) - Next commutes with Always
            "FixedPoint.TLA_next_always_comm",
            // ○(◇P) = ◇(○P) - Next commutes with Eventually
            "FixedPoint.TLA_next_eventually_comm",
            // ○(P ∧ Q) = ○P ∧ ○Q - Next distributes over conjunction
            "FixedPoint.TLA_next_and",
            // ○(P ∨ Q) = ○P ∨ ○Q - Next distributes over disjunction
            "FixedPoint.TLA_next_or",
            // ○¬P = ¬○P - Next commutes with negation
            "FixedPoint.TLA_next_not",
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        // ================================================================
        // Parameterized Fixed Points
        // ================================================================
        for name in &[
            // Fixed points with parameters
            "FixedPoint.lfp_param", // lfp over parameterized function
            "FixedPoint.gfp_param", // gfp over parameterized function
            // Substitution lemmas
            "FixedPoint.lfp_subst", // Substituting in lfp
            "FixedPoint.gfp_subst", // Substituting in gfp
        ] {
            self.add_decl(Declaration::Axiom {
                name: Name::from_string(name),
                level_params: vec![u.clone()],
                type_: type_u.clone(),
            })?;
        }

        self.fixed_point_init = true;
        Ok(())
    }

    /// Check if Fixed Point Theory module has been initialized
    ///
    /// # Contract
    ///
    /// ENSURES: Returns `true` iff `init_fixed_point` has completed successfully
    /// ENSURES: Pure - no side effects
    #[allow(dead_code)] // Used by integration tests
    pub(crate) fn has_fixed_point(&self) -> bool {
        self.fixed_point_init
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::test_helpers::assert_const;

    #[test]
    fn test_fixed_point_init() {
        let mut env = Environment::new();
        assert!(!env.has_fixed_point());

        env.init_fixed_point()
            .expect("init_fixed_point should succeed");
        assert!(env.has_fixed_point());

        assert_const(&env, "FixedPoint.lfp");
        assert_const(&env, "FixedPoint.gfp");
        assert_const(&env, "FixedPoint.lfp_unfold");
        assert_const(&env, "FixedPoint.gfp_unfold");
        assert_const(&env, "FixedPoint.lfp_induction");
        assert_const(&env, "FixedPoint.gfp_coinduction");
        assert_const(&env, "FixedPoint.Monotone");
    }

    #[test]
    fn test_fixed_point_idempotent() {
        let mut env = Environment::new();

        env.init_fixed_point().expect("first init should succeed");
        env.init_fixed_point()
            .expect("second init should also succeed (idempotent)");

        assert!(env.has_fixed_point());
    }

    #[test]
    fn test_tla_temporal_axioms() {
        let mut env = Environment::new();
        env.init_fixed_point()
            .expect("init_fixed_point should succeed");

        assert_const(&env, "FixedPoint.TLA_next");
        assert_const(&env, "FixedPoint.TLA_eventually");
        assert_const(&env, "FixedPoint.TLA_always");
        assert_const(&env, "FixedPoint.TLA_leads_to");
    }

    #[test]
    fn test_tla_next_operator() {
        let mut env = Environment::new();
        env.init_fixed_point()
            .expect("init_fixed_point should succeed");

        let info = env
            .get_const(&Name::from_string("FixedPoint.TLA_next"))
            .expect("TLA_next operator must exist for temporal unfolding");
        assert_eq!(
            info.name,
            Name::from_string("FixedPoint.TLA_next"),
            "TLA_next name mismatch"
        );
    }

    #[test]
    fn test_fixed_point_key_types_well_formed() {
        use crate::expr::ExprKind;
        use crate::level::Level;
        use crate::tc::TypeChecker;

        let mut env = Environment::new();
        env.init_fixed_point().unwrap();
        let tc = TypeChecker::new(&env);

        for name in &[
            "FixedPoint.lfp",
            "FixedPoint.gfp",
            "FixedPoint.Monotone",
            "FixedPoint.TLA_next",
        ] {
            let expr = Expr::const_(Name::from_string(name), vec![Level::zero()]);
            let ty = tc
                .infer_type(&expr)
                .unwrap_or_else(|e| panic!("{name}: tc.infer_type failed: {e}"));
            assert!(
                matches!(&ty.kind, ExprKind::Sort(_)),
                "{name}: expected Sort type, got {ty:?}"
            );
        }

        // Verify universe level params
        let lfp_info = env
            .get_const(&Name::from_string("FixedPoint.lfp"))
            .expect("FixedPoint.lfp");
        assert!(
            !lfp_info.level_params.is_empty(),
            "FixedPoint.lfp should have universe parameters"
        );
    }
}
