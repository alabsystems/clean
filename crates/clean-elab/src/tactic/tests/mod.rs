// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
mod helpers;

// Re-export test helpers for test submodules
// (advanced.rs, arithmetic.rs, conv.rs, library_search.rs, mathlib_tactics.rs,
//  pattern_tactics.rs, propositional.rs, search_tactics.rs, simp.rs, etc.)
pub(super) use self::helpers::*;
use clean_kernel::env::Declaration;
// Re-export for test submodules (they use `use super::*`)
pub(super) use clean_kernel::{Environment, FVarId, TypeChecker};

/// Test-only witness for the retired target-rewrite compatibility helpers.
///
/// `#2580` removes the production wrapper from `goal_ops.rs`, but the tests
/// still exercise the historical fallback/accounting behavior from `tests/`.
pub(super) enum TargetRewriteWitness {
    EqualityProof {
        tactic_name: &'static str,
        eq_proof: Expr,
    },
    TrustedFallback {
        tactic_name: &'static str,
    },
}

fn require_const(env: &Environment, constant: &str) -> Result<(), TacticError> {
    if env.get_const(&Name::from_string(constant)).is_some() {
        Ok(())
    } else {
        Err(TacticError::EnvironmentMissing {
            constant: constant.to_string(),
        })
    }
}

impl ProofState {
    pub(super) fn replace_target_with_witness(
        &mut self,
        new_target: Expr,
        witness: TargetRewriteWitness,
    ) -> Result<(), TacticError> {
        match self.replace_target_def_eq(new_target.clone()) {
            Ok(()) => Ok(()),
            Err(TacticError::GoalMismatch(_)) => match witness {
                TargetRewriteWitness::EqualityProof {
                    tactic_name,
                    eq_proof,
                } => {
                    tracing::debug!(
                        tactic = tactic_name,
                        "using explicit equality proof for target rewrite"
                    );
                    self.replace_target_eq(new_target, eq_proof)
                }
                TargetRewriteWitness::TrustedFallback { tactic_name } => {
                    require_const(self.env(), "Eq")?;

                    let goal = self.current_goal().ok_or(TacticError::NoGoals)?.clone();
                    let old_target = self.metas.instantiate(&goal.target);

                    // Sort check (Wave 88): the trusted fallback wires the
                    // rewrite through `Eq.{1} Prop old_target new_target`,
                    // which is only well-typed when BOTH targets live in
                    // `Prop`. If `old_target` and `new_target` live in
                    // different sorts (e.g. `Prop` vs `Type u`), the fake
                    // equality proof would silently introduce a sort
                    // mismatch that the kernel cannot verify and that the
                    // trusted-axiom audit cannot retroactively justify.
                    // Fail-closed here so callers see a structured
                    // `TypeMismatch` instead.
                    let (old_sort, new_sort) = {
                        let tc = TypeChecker::new(self.env());
                        let os = tc.infer_sort(&old_target).map_err(|e| {
                            TacticError::TypeCheckFailed(format!(
                                "{tactic_name}: cannot infer sort of old target: {e}"
                            ))
                        })?;
                        let ns = tc.infer_sort(&new_target).map_err(|e| {
                            TacticError::TypeCheckFailed(format!(
                                "{tactic_name}: cannot infer sort of new target: {e}"
                            ))
                        })?;
                        (os, ns)
                    };
                    let old_is_prop = matches!(&old_sort, Level::Zero);
                    let new_is_prop = matches!(&new_sort, Level::Zero);
                    if old_is_prop != new_is_prop {
                        return Err(TacticError::TypeMismatch {
                            expected: format!("sort {old_sort:?} (matching old target)"),
                            actual: format!("sort {new_sort:?} (of new target)"),
                        });
                    }

                    let eq_ty = Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::const_(
                                    Name::from_string("Eq"),
                                    vec![Level::succ(Level::zero())],
                                ),
                                Expr::prop(),
                            ),
                            old_target,
                        ),
                        new_target.clone(),
                    );

                    tracing::warn!(
                        tactic = tactic_name,
                        "using trustedArith to connect simplified target"
                    );
                    let trusted_arith_name = Name::from_string("trustedArith");
                    let has_trusted_arith = self.env().get_const(&trusted_arith_name).is_some();
                    let trusted_proof =
                        arith_linarith::make_trusted_arith_term_untracked(self.env(), &eq_ty);
                    self.replace_target_eq(new_target, trusted_proof).map(|()| {
                        if has_trusted_arith {
                            arith_linarith::record_target_rewrite_trusted_arith_fallback(
                                self,
                                tactic_name,
                            );
                        } else {
                            self.record_sorry();
                        }
                    })
                }
            },
            Err(err) => Err(err),
        }
    }

    pub(super) fn replace_target_with_trusted_fallback(
        &mut self,
        new_target: Expr,
        tactic_name: &'static str,
    ) -> Result<(), TacticError> {
        self.replace_target_with_witness(
            new_target,
            TargetRewriteWitness::TrustedFallback { tactic_name },
        )
    }
}

/// Build `@LE.le.{0} Nat instLENat lhs rhs` — kernel-correct form with proper
/// typeclass instance. Shared helper for arithmetic proof-type tests.
///
/// Delegates to [`super::tc_app::nat_le_tc`] (F1 consolidation from #2151).
pub(super) fn make_nat_le_tc(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::nat_le_tc(lhs, rhs)
}

pub(super) fn setup_env() -> Environment {
    let mut env = Environment::new();

    // Add a simple type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add a term of that type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("a"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("A"), vec![]),
    })
    .unwrap();

    // Add another type
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("B"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add a function A → B
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("B"), vec![]),
        ),
    })
    .unwrap();

    env
}

pub(super) fn setup_env_with_and_or() -> Environment {
    let mut env = Environment::new();
    env.init_and().unwrap();
    env.init_classical().unwrap();

    let prop = Expr::prop();

    // Propositions
    for name in ["P", "Q"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: prop.clone(),
        })
        .unwrap();
    }

    // Proof witnesses
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("p"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("P"), vec![]),
    })
    .unwrap();
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("q"),
        level_params: vec![],
        type_: Expr::const_(Name::from_string("Q"), vec![]),
    })
    .unwrap();

    env
}

pub(super) fn setup_env_with_prop_ext() -> Environment {
    let mut env = Environment::new();
    env.init_true_false().unwrap();
    env.init_and().unwrap();
    env.init_iff().unwrap();
    env.init_classical().unwrap();
    env.init_exists().unwrap();
    env.init_propext().unwrap();
    env
}

pub(super) fn setup_env_with_nat() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env
}

/// Nat environment with Even/Odd parity declarations and the Nat.even_and_odd_elim
/// bridge theorem. Required for mathverse parity contradiction end-to-end tests after
/// the modular proof-carry work (#2564) made mathverse fail-closed without the bridge.
pub(super) fn setup_env_with_parity_bridge() -> Environment {
    let mut env = setup_env_with_nat();
    env.init_true_false().unwrap();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_to_prop = Expr::arrow(nat.clone(), Expr::prop());
    for name in ["Even", "Odd"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: nat_to_prop.clone(),
        })
        .unwrap();
    }
    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
    let even_bvar = Expr::app(
        Expr::const_(Name::from_string("Even"), vec![]),
        Expr::bvar(0),
    );
    let odd_bvar = Expr::app(
        Expr::const_(Name::from_string("Odd"), vec![]),
        Expr::bvar(1),
    );
    let elim_ty = Expr::pi(
        BinderInfo::Default,
        nat,
        Expr::pi(
            BinderInfo::Default,
            even_bvar,
            Expr::pi(BinderInfo::Default, odd_bvar, false_ty),
        ),
    );
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Nat.even_and_odd_elim"),
        level_params: vec![],
        type_: elim_ty,
    })
    .unwrap();

    env
}

/// Environment with classical logic + Int ordering (for abs_cases, numeric tactics).
///
/// Provides: Or, Or.rec, Classical.em, Int, instLEInt, GE.ge, plus B : Prop.
/// Part of #2154: abs_cases migration to checked close_goal requires the kernel
/// to type-check proof terms containing these constants.
pub(super) fn setup_env_with_int_ord() -> Environment {
    let mut env = Environment::new();
    env.init_int_ord_lemmas().unwrap(); // chains: init_int_ord → init_le, init_lt, init_int_arith
    env.init_ge().unwrap();

    // B : Prop (target for abs_cases — Or.rec eliminates into Prop only)
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("B"),
        level_params: vec![],
        type_: Expr::prop(),
    })
    .unwrap();

    env
}

/// Environment with Bool + PUnit as proper inductives (for fin_cases type-checking).
///
/// Provides: Bool (with casesOn, rec), PUnit (with casesOn, rec),
/// plus P : Bool → Prop and Q : PUnit.{0} → Prop as test predicates.
/// Part of #2154 Wave 10: fin_cases migration from close_goal_unchecked
/// requires the kernel to type-check casesOn proof terms.
pub(super) fn setup_env_for_finite_cases() -> Environment {
    let mut env = Environment::new();
    env.init_bool().unwrap();
    env.init_punit().unwrap();

    // P : Bool → Prop (predicate for Bool fin_cases tests)
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::arrow(bool_ty, Expr::prop()),
    })
    .unwrap();

    // Q : PUnit.{0} → Prop (predicate for PUnit fin_cases tests)
    let punit_ty = Expr::const_(Name::from_string("PUnit"), vec![Level::zero()]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Q"),
        level_params: vec![],
        type_: Expr::arrow(punit_ty, Expr::prop()),
    })
    .unwrap();

    env
}

/// Setup environment with Eq + Eq.subst + Eq.symm + N + x,y,z:N + P:N→Prop
///
/// Shared helper for rewrite, equality, and at-location test files.
/// Extracted from core.rs during #307 large file split.
pub(super) fn setup_env_with_full_eq() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Add a base type N
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("N"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constants x, y, z : N
    for name in ["x", "y", "z"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("N"), vec![]),
        })
        .unwrap();
    }

    // Add predicate P : N → Prop
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("P"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("N"), vec![]),
            Expr::prop(),
        ),
    })
    .unwrap();

    env
}

/// Helper to make `@Eq.{1} N lhs rhs` expression
pub(super) fn make_eq_n(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                Expr::const_(Name::from_string("N"), vec![]),
            ),
            lhs,
        ),
        rhs,
    )
}

/// Helper to make `P(t)` expression
pub(super) fn make_p(t: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("P"), vec![]), t)
}

/// Build `@Eq.{1} ty lhs rhs` — generic equality expression at universe 1.
///
/// Shared helper: extracted from core.rs, decide_eq_noconfusion_shape.rs, sorry_absence.rs
/// where it was defined identically in each file.
pub(super) fn make_eq(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                ty,
            ),
            lhs,
        ),
        rhs,
    )
}

/// Reset all proof counters (sorry + trustedArith + trustedAy) for test isolation.
///
/// Shared helper: extracted from sorry_absence.rs + trusted_axiom_state.rs
/// where it was defined identically in each file.
pub(super) fn reset_all_counters() {
    reset_sorry_counter();
    reset_arith_counter();
    reset_ay_counter();
}

pub(super) fn tracked_arith_location_count(location: &str) -> u64 {
    arith_linarith::arith_locations()
        .unwrap_or_default()
        .get(location)
        .copied()
        .unwrap_or(0)
}

pub(super) fn direct_arith_file_count(file: &str) -> u64 {
    let direct_file_prefix = format!("{file}:");
    arith_linarith::arith_locations()
        .unwrap_or_default()
        .into_iter()
        .filter(|(location, _)| location.starts_with(&direct_file_prefix))
        .map(|(_, count)| count)
        .sum()
}

/// Snapshot trusted-axiom counters before a tactic call. Used with
/// `assert_no_trusted_axiom_usage` to detect counter increments via
/// before/after diff (immune to concurrent non-serial test races).
///
/// Shared helper: extracted from sorry_absence.rs for reuse across test files.
pub(super) fn axiom_snapshot() -> (u64, u64) {
    (arith_proof_count(), ay_proof_count())
}

/// Assert that no trusted-axiom redirections occurred during a tactic invocation.
///
/// Shared helper: extracted from sorry_absence.rs for reuse across test files.
pub(super) fn assert_no_trusted_axiom_usage(name: &str, desc: &str, before: (u64, u64)) {
    let (a, z) = (arith_proof_count() - before.0, ay_proof_count() - before.1);
    assert_eq!(
        a, 0,
        "TRUSTED AXIOM LEAK: {name} used {a} trustedArith to prove {desc}"
    );
    assert_eq!(
        z, 0,
        "TRUSTED AXIOM LEAK: {name} used {z} trustedAy to prove {desc}"
    );
}

/// Environment with Eq + type A + constants a,b,c:A + function f:A→A.
///
/// Shared helper: extracted from core.rs + sorry_absence.rs (which had a subset
/// without f). Using the superset version — extra declarations don't affect
/// tests that don't reference them.
pub(super) fn setup_env_with_eq() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();

    // Add a base type A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .unwrap();

    // Add constants a, b, c : A
    for name in ["a", "b", "c"] {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(name),
            level_params: vec![],
            type_: Expr::const_(Name::from_string("A"), vec![]),
        })
        .unwrap();
    }

    // Add function f : A → A
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("f"),
        level_params: vec![],
        type_: Expr::arrow(
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::const_(Name::from_string("A"), vec![]),
        ),
    })
    .unwrap();

    env
}

mod advanced;
mod aesop_backtrack;
mod aesop_cases_args;
mod aesop_constructors;
mod aesop_destruct;
mod aesop_forward;
mod aesop_index_modes;
mod aesop_mathlib;
mod aesop_meta_merge;
mod aesop_priority;
mod aesop_properties;
mod aesop_search_state;
mod aesop_simp;
mod aesop_simp_config;
mod aesop_strategy;
mod aesop_unfold_tactic;
mod app_spine_regressions;
mod apply_fun_goal_regressions;
mod apply_fun_proof_carry;
mod arithmetic;
mod at_location;
#[cfg(feature = "ay-smt")]
mod ay_lra_linarith;
mod ay_registry_dispatch;
#[cfg(feature = "ay-smt")]
mod ay_smt;
#[cfg(feature = "ay-smt")]
mod ay_smt_real;
mod builtins_registry;
mod bypass_ratchet;
mod cert_simp;
mod certified_arithmetic_fail_closed;
mod classical;
mod close_fvars;
mod conv;
mod conv_ext;
mod conv_focus_rewrite_edges;
mod conv_proof_carry;
mod conv_witness_boundary;
mod core;
mod decide_ay_guards;
mod decide_eq_noconfusion_shape;
mod decide_eq_wrapper_parity;
mod decide_fallback_routing;
mod domain_profile;
mod equality;
mod extensionality;
mod field_simp_proof_carry;
mod finite_cases_dependent_fin;
mod finite_cases_proof_chain;
mod have_let;
mod infer_instance;
mod instance_registration;
mod let_bindings;
mod library_search;
mod linarith_contradiction_closeout;
mod linarith_proof_nat_acc;
mod linarith_proof_type;
mod linarith_rat_kernel_theorem;
mod linarith_real_proof_carry;
mod linear_combination_proof;
mod linear_combination_proof_cancellation;
mod linear_combination_proof_real;
mod linear_combination_proof_real_distrib;
mod linear_combination_proof_zero_fractional;
mod local_ops;
mod mathlib_tactics;
mod mathverse_modular_proof_carry;
mod mathverse_proof_carry;
mod mono_tactics;
mod nat_numeral_ofnat;
mod native_decide;
mod nlinarith_proof_carry;
mod omega_farkas_goal;
mod omega_hyp_eq_adversarial;
mod omega_int_equality;
mod omega_nat_equality_direct;
mod omega_nat_equality_hyps;
mod omega_nat_inequality_direct;
mod omega_nat_minmax_direct;
mod omega_nat_sub_direct;
mod pattern_tactics;
mod perf_proofs;
mod polynomial_constant_coeff;
mod polyrith_proof_carry;
mod polyrith_proof_carry_denominator;
mod polyrith_proof_carry_int_weighted;
mod polyrith_proof_carry_multi_hyp;
mod polyrith_proof_carry_rat;
mod polyrith_proof_carry_real;
mod positivity_regressions;
mod proj_mdata_traversal;
mod project_mathverse;
mod proof_scope_wideners;
mod propositional;
mod proptest_simp_soundness;
mod reduce_eq;
mod replace_target;
mod replace_target_witness;
mod rewrite_subst;
mod rfl_prod_cases_on;
mod ring_hadd_hmul;
mod ring_hadd_real_env;
mod ring_identity;
mod ring_identity_int;
mod ring_kernel_proof;
mod ring_literals;
mod ring_mixed_ops;
mod ring_proof_carry;
mod ring_proof_sort;
mod ring_proof_surface;
mod ring_roundtrip;
mod search_tactics;
mod seq_focus;
mod simp;
mod simp_local_context;
mod simp_multi_binder_proof;
mod simp_proof_carry;
mod simp_unfold_defs;
mod simp_universe_levels;
mod simproc;
mod sorry_absence;
mod sorry_census;
mod sorry_runtime;
mod surface_expr_to_name;
mod tactic_parity_registry;
mod trusted_arith;
mod trusted_axiom_fallback_sites;
mod trusted_axiom_state;
mod trusted_ay;
mod trusted_ratchet;
mod unfold_tests;
mod unfold_universe_levels;
