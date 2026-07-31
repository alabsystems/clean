// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse tactic (linear integer arithmetic)
//!
//! Implements the Omega test for integer linear arithmetic including:
//! - Certified proof reconstruction
//! - Modular arithmetic reasoning
//! - Parity and divisibility proofs
//!
//! Expression parsing is in `arith_mathverse_parse`.
//! Proof reconstruction is in `arith_mathverse_proof`.

mod bmod_elim;
mod case_split;
mod certified;
mod equality_solver;
mod fail_closed;
mod gcd_normalize;
mod le_solver;
mod nat_div_mod;
mod nat_sub;

pub(crate) use certified::{extract_certified_mathverse_constraints, mathverse_check_certified};

use clean_kernel::{Expr, FVarId};

use super::arith_linarith::{fourier_motzkin_check, FMResult, LinarithCertificate};
use super::arith_mathverse_proof::{
    build_mathverse_proof, build_modular_mathverse_proof, MathverseProofOutcome,
};
use super::arithmetic::{LinearConstraint, LinearExpr};
use super::{decide, Goal, ProofState, TacticError, TacticResult};
use fail_closed::certified_arithmetic_contradiction_without_kernel_proof;

// Re-export parsing functions for tests and other modules
pub(crate) use super::arith_mathverse_parse::{
    expr_to_mathverse_constraint, negate_mathverse_constraint,
};

#[cfg(test)]
pub(crate) use fail_closed::test_only_certified_arithmetic_contradiction_without_kernel_proof;

// =============================================================================
// Mathverse tactic types
// =============================================================================

/// Certificate for mathverse proof reconstruction.
///
/// Similar to LinarithCertificate, this tracks which hypotheses contribute
/// to proving the contradiction and with what coefficients.
/// The mathverse tactic uses this to attempt generating kernel-valid proofs
/// instead of using `sorry`.
#[derive(Debug, Clone)]
pub struct MathverseCertificate {
    /// Coefficients for each original hypothesis, indexed by hypothesis position.
    /// A coefficient of 0 means the hypothesis wasn't used.
    pub coefficients: Vec<i128>,
    /// Whether the goal negation was used
    pub uses_goal_negation: bool,
    /// The type of contradiction found
    pub contradiction_type: MathverseContradictionType,
}

/// The type of contradiction found by mathverse
#[derive(Debug, Clone)]
pub enum MathverseContradictionType {
    /// Direct arithmetic contradiction (e.g., 1 ≤ 0)
    Arithmetic,
    /// Parity contradiction (e.g., even = odd)
    Parity,
    /// Divisibility contradiction (e.g., n | k but n ∤ k)
    Divisibility,
    /// General linear combination yields contradiction
    LinearCombination,
}

impl MathverseCertificate {
    /// Create an empty certificate
    ///
    /// REQUIRES: `num_hypotheses >= 0`
    /// ENSURES: `result.coefficients.len() == num_hypotheses`
    /// ENSURES: All coefficients are 0
    /// ENSURES: `result.uses_goal_negation == false`
    /// ENSURES: `result.contradiction_type` is `Arithmetic`
    pub fn new(num_hypotheses: usize) -> Self {
        Self {
            coefficients: vec![0_i128; num_hypotheses],
            uses_goal_negation: false,
            contradiction_type: MathverseContradictionType::Arithmetic,
        }
    }

    /// Create a certificate from a linarith certificate
    ///
    /// REQUIRES: `linarith_cert` is a valid `LinarithCertificate`
    /// ENSURES: `result.coefficients == linarith_cert.coefficients`
    /// ENSURES: `result.uses_goal_negation == true` (linarith always negates goal)
    /// ENSURES: `result.contradiction_type` is `LinearCombination`
    pub fn from_linarith(linarith_cert: &LinarithCertificate) -> Self {
        Self {
            coefficients: linarith_cert.coefficients.clone(),
            uses_goal_negation: true, // linarith always negates goal
            contradiction_type: MathverseContradictionType::LinearCombination,
        }
    }

    /// Check if the certificate is valid (all coefficients non-negative)
    ///
    /// ENSURES: Returns `true` iff every coefficient in `self.coefficients` is `>= 0`
    /// ENSURES: Does not check `uses_goal_negation` or `contradiction_type`
    pub fn is_valid(&self) -> bool {
        self.coefficients.iter().all(|&c| c >= 0)
    }
}

/// A constraint with its certificate for mathverse
#[derive(Debug, Clone)]
pub struct CertifiedMathverseConstraint {
    /// The constraint
    pub constraint: OmegaConstraint,
    /// The certificate
    pub certificate: MathverseCertificate,
}

impl CertifiedMathverseConstraint {
    /// Create from an original hypothesis
    ///
    /// REQUIRES: `hyp_index < num_hypotheses`
    /// ENSURES: `result.certificate.coefficients[hyp_index] == 1`
    /// ENSURES: All other coefficients are 0
    /// ENSURES: `result.certificate.coefficients.len() == num_hypotheses`
    pub fn from_hypothesis(
        constraint: OmegaConstraint,
        hyp_index: usize,
        num_hypotheses: usize,
    ) -> Self {
        let mut cert = MathverseCertificate::new(num_hypotheses);
        cert.coefficients[hyp_index] = 1;
        Self {
            constraint,
            certificate: cert,
        }
    }

    /// Create from negated goal
    ///
    /// ENSURES: `result.certificate.uses_goal_negation == true`
    /// ENSURES: All coefficients are 0 (goal negation, not a hypothesis)
    /// ENSURES: `result.certificate.coefficients.len() == num_hypotheses`
    pub fn from_negated_goal(constraint: OmegaConstraint, num_hypotheses: usize) -> Self {
        let mut cert = MathverseCertificate::new(num_hypotheses);
        cert.uses_goal_negation = true;
        Self {
            constraint,
            certificate: cert,
        }
    }

    /// Create from an implicit Nat non-negativity bound `0 ≤ v`.
    ///
    /// These synthetic constraints make the rational/integer refutation see the
    /// `v ≥ 0` fact that every Nat variable carries implicitly, so a goal like
    /// `(h : a + 2 ≤ b) ⊢ b ≥ 2` (UNSAT only once `a ≥ 0` is added) is found
    /// UNSAT instead of `Sat`. The certificate carries all-zero coefficients and
    /// `uses_goal_negation == false`: the implicit bound is neither a tracked
    /// hypothesis nor the negated goal, so it never perturbs hypothesis
    /// attribution. The downstream Farkas-with-goal proof builder
    /// re-derives the needed `Nat.zero_le v` facts independently from the linear
    /// residual and the assembled term is kernel-rechecked, so this synthetic
    /// constraint only affects the *search*, never the trusted certificate.
    ///
    /// ENSURES: All coefficients are 0 and `uses_goal_negation == false`
    /// ENSURES: `result.certificate.coefficients.len() == num_hypotheses`
    pub fn from_implicit_nonneg(constraint: OmegaConstraint, num_hypotheses: usize) -> Self {
        Self {
            constraint,
            certificate: MathverseCertificate::new(num_hypotheses),
        }
    }
}

/// Result of certified mathverse check
#[derive(Debug)]
pub enum MathverseCertifiedResult {
    /// Unsatisfiable with certificate
    Unsat(MathverseCertificate),
    /// Satisfiable (no contradiction)
    Sat,
    /// Could not determine
    Unknown,
}

/// Mathverse constraint representation
#[derive(Debug, Clone)]
pub enum OmegaConstraint {
    /// a₁x₁ + a₂x₂ + ... + c ≤ 0
    Le(LinearExpr),
    /// a₁x₁ + a₂x₂ + ... + c < 0
    Lt(LinearExpr),
    /// a₁x₁ + a₂x₂ + ... + c = 0
    Eq(LinearExpr),
    /// a₁x₁ + a₂x₂ + ... + c ≠ 0
    Ne(LinearExpr),
    /// x ≡ r (mod m)
    Mod {
        var: usize,
        remainder: i64,
        modulus: i64,
    },
    /// ¬(m ∣ x), i.e., x % m ≠ 0
    /// Represents `Not (Dvd.dvd m x)` - x is NOT divisible by m
    NotMod { var: usize, modulus: i64 },
    /// expr ≡ r (mod m) where expr is a general linear expression
    /// Represents `(a + b + ...) % m = r` or more complex modular constraints
    LinearMod {
        expr: LinearExpr,
        remainder: i64,
        modulus: i64,
    },
    /// ¬(expr ≡ r (mod m)) - negated modular equality with arbitrary remainder
    /// Represents `(a + b + ...) % m ≠ r`
    NotLinearMod {
        expr: LinearExpr,
        remainder: i64,
        modulus: i64,
    },
}

fn close_certified_mathverse_contradiction(
    state: &mut ProofState,
    goal: &Goal,
    certificate: &MathverseCertificate,
    hypothesis_fvars: &[FVarId],
) -> TacticResult {
    match &certificate.contradiction_type {
        MathverseContradictionType::Arithmetic | MathverseContradictionType::LinearCombination => {
            // General Farkas-with-goal route (Nat): the certified replay below
            // only combines hypotheses with each other and drops the negated
            // goal, so genuine `hyp + neg_goal` certificates (t1/t2/t5) never
            // produce the target term. Try the by-contradiction Farkas builder
            // first; its term is re-checked by `close_goal`, so a wrong
            // combination fails closed. Only fires when the certificate's UNSAT
            // witness uses the negated goal.
            if let Some(proof) = super::arith_linarith_farkas_goal::try_build_farkas_goal_proof(
                state,
                goal,
                certificate,
                hypothesis_fvars,
            ) {
                match state.close_goal(goal, proof) {
                    Ok(()) => return Ok(()),
                    Err(err) => tracing::debug!(
                        "mathverse: farkas-with-goal proof built but close_goal rejected: {err:?}"
                    ),
                }
            }

            let env = state.env().clone();
            let arithmetic_reason = if let Some(proof) =
                build_mathverse_proof(state, goal, certificate, hypothesis_fvars, &env)
            {
                match state.close_goal(goal, proof) {
                    Ok(()) => return Ok(()),
                    Err(err) => {
                        tracing::debug!(
                            "mathverse: build_mathverse_proof succeeded but close_goal rejected: {err:?}"
                        );
                        format!("close_goal rejected arithmetic proof: {err}")
                    }
                }
            } else {
                tracing::debug!(
                    "mathverse: build_mathverse_proof returned None for certified mathverse"
                );
                "build_mathverse_proof returned None".to_string()
            };

            if decide(state).is_ok() {
                return Ok(());
            }

            certified_arithmetic_contradiction_without_kernel_proof(arithmetic_reason)
        }
        MathverseContradictionType::Parity | MathverseContradictionType::Divisibility => {
            let env = state.env().clone();
            let modular_reason = match build_modular_mathverse_proof(
                state,
                goal,
                certificate,
                hypothesis_fvars,
                &env,
            ) {
                MathverseProofOutcome::Proof(proof) => match state.close_goal(goal, proof) {
                    Ok(()) => return Ok(()),
                    Err(err) => {
                        tracing::debug!(
                            "mathverse: modular proof reconstruction succeeded but close_goal rejected: {err:?}"
                        );
                        format!("close_goal rejected modular proof: {err}")
                    }
                },
                MathverseProofOutcome::UnsupportedModularProof { reason } => reason,
            };

            if decide(state).is_ok() {
                return Ok(());
            }

            Err(TacticError::ArithmeticFailed {
                tactic: "mathverse".into(),
                reason: format!(
                    "certified modular contradiction has no kernel proof ({modular_reason})"
                ),
            })
        }
    }
}

/// `true` when `ty` is `¬(rel)` for a linear comparison `rel`
/// (`≤` / `<` / `≥` / `>` / `=`) — the shapes `push_neg` can flip into a
/// positive relation. Restricting to these keeps the normalization from
/// over-transforming unrelated negations (`¬(P ∧ Q)`, `¬∃`, …) that the omega
/// solver could not use.
fn is_negated_relation(ty: &Expr) -> bool {
    let Some(inner) = super::match_not(ty) else {
        return false;
    };
    super::match_le(&inner).is_some()
        || super::match_lt(&inner).is_some()
        || super::match_ge(&inner).is_some()
        || super::match_gt(&inner).is_some()
        || super::match_eq(&inner).is_some()
}

/// Normalize negated linear relations `¬(rel)` in hypothesis and goal position
/// into their positive equivalents, using the proof-carrying `push_neg` /
/// `push_neg_at` rewrites.
///
/// - `¬(a ≤ 2)` hypothesis → `2 < a`; `¬(a < b)` → `b ≤ a`, etc.
/// - `¬(a ≥ 3)` goal → `a < 3`, `¬(a > b)` → `a ≤ b`.
///
/// Best-effort and non-fatal: each rewrite is proof-carrying (threaded through
/// `propext` + `Eq.subst`, kernel-rechecked by `replace_local_decl_with_cast` /
/// `replace_target_eq`), so it can only change the *form* the downstream solver
/// sees, never soundness. Any individual rewrite that does not apply (or a goal
/// with no active goals) is silently skipped — omega then proceeds on whatever
/// hypotheses / goal remain.
fn normalize_negated_relations(state: &mut ProofState) {
    // Hypotheses first: collect the names of `¬(rel)` hypotheses up front (the
    // local context is mutated as we rewrite), then flip each one.
    let Some(goal) = state.current_goal().cloned() else {
        return;
    };
    let neg_hyp_names: Vec<String> = goal
        .local_ctx
        .iter()
        .filter(|d| is_negated_relation(&d.ty))
        .map(|d| d.name.clone())
        .collect();
    for name in neg_hyp_names {
        // `push_neg_at` leaves the state unchanged on failure (contract), so a
        // hypothesis it cannot flip is simply left as-is.
        let _ = super::push_neg_at(state, &name);
    }

    // Goal: flip a `¬(rel)` target into its positive relation.
    if let Some(goal) = state.current_goal() {
        let target = state.metas.instantiate(&goal.target);
        if is_negated_relation(&target) {
            let _ = super::push_neg(state);
        }
    }
}

// =============================================================================
// Mathverse tactic entry point
// =============================================================================

/// Goal-driven direct Nat inequality reconstruction (bounded slices A + B).
///
/// Attempts [`super::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps`]
/// against the current goal and its local hypotheses, then re-checks the
/// synthesized term with `close_goal` (a full kernel check). Returns `Ok(())`
/// only if a genuine kernel-valid proof was produced and accepted.
///
/// Soundness: the direct prover returns `None` for false / unmatched goals, and
/// `close_goal` rejects any term whose type is not def-eq to the goal. No false
/// goal can be closed here.
fn try_direct_nat_reconstruction(state: &mut ProofState, goal: &Goal) -> TacticResult {
    let direct_hyps: Vec<(Expr, Expr)> = goal
        .local_ctx
        .iter()
        .map(|d| (Expr::fvar(d.fvar), d.ty.clone()))
        .collect();
    // Env-aware equality-hypothesis goal solver first: this is the only place
    // with access to `state.env()`, which the disequality (`≠`) residual needs
    // (it builds a ground `Nat.noConfusion` witness). Equality / inequality
    // goals are handled by the env-free `try_prove_nat_inequality_direct_with_hyps`
    // below as well, but routing `≠` goals here gives them the environment.
    let env = state.env().clone();
    let proof =
        super::eq_goal_solver::try_prove_goal_via_eq_hyps(&goal.target, &direct_hyps, Some(&env))
            .or_else(|| {
                super::arith_linarith_nat_direct::try_prove_nat_inequality_direct_with_hyps(
                    &goal.target,
                    &direct_hyps,
                )
            })
            // Negated-equality goal `¬(a = k)` / `a ≠ k` closed from a bounding
            // inequality hypothesis whose range excludes `k` (e.g. `a < 3 ⊢ ¬(a=5)`).
            .or_else(|| {
                super::eq_goal_solver::try_prove_not_eq_via_bound_hyp(&goal.target, &direct_hyps)
            });
    let Some(proof) = proof else {
        return Err(TacticError::ArithmeticFailed {
            tactic: "omega".to_string(),
            reason: "no direct Nat reconstruction for goal".to_string(),
        });
    };
    state
        .close_goal(goal, proof)
        .map_err(|e| TacticError::ArithmeticFailed {
            tactic: "omega".to_string(),
            reason: format!("direct Nat reconstruction rejected by close_goal: {e:?}"),
        })
}

/// Goal-driven direct **Int** reconstruction (linear equalities, `≤`/`≥`
/// antisymmetry, and `False` from contradictory equality hypotheses).
///
/// Attempts, in order: a free-variable linear `Int` equality
/// ([`super::arith_linarith_int_eq::try_prove_int_equality`]); `a = b` from a
/// pair of `Int` bounds via `Int.le_antisymm`
/// ([`super::arith_linarith_int_eq::try_prove_int_eq_via_le_antisymm`]); and a
/// `False` goal from two contradictory `Int` equality hypotheses
/// ([`super::arith_linarith_int_eq::try_prove_int_false_from_eq_hyps`]). The
/// synthesized term is re-checked by `close_goal` (a full kernel check), so a
/// wrong or false-goal candidate is rejected — never trusted.
///
/// Soundness: each Int prover returns `None` for false / unmatched goals and
/// gates equalities on a linear-form equality check; `close_goal` re-checks the
/// exact term against the goal. No false goal can be closed here. Zero
/// domain-specific axioms (every constant used is a foundational prelude lemma /
/// recursor).
fn try_int_reconstruction(state: &mut ProofState, goal: &Goal) -> TacticResult {
    let direct_hyps: Vec<(Expr, Expr)> = goal
        .local_ctx
        .iter()
        .map(|d| (Expr::fvar(d.fvar), d.ty.clone()))
        .collect();
    let env = state.env().clone();

    let proof = super::arith_linarith_int_eq::try_prove_int_equality(&goal.target)
        .or_else(|| {
            super::arith_linarith_int_eq::try_prove_int_eq_via_le_antisymm(
                &goal.target,
                &direct_hyps,
            )
        })
        // `False` goal from contradictory `Int` equality hypotheses.
        .or_else(|| {
            if is_false_target(&goal.target) {
                super::arith_linarith_int_eq::try_prove_int_false_from_eq_hyps(&env, &direct_hyps)
            } else {
                None
            }
        });

    let Some(proof) = proof else {
        return Err(TacticError::ArithmeticFailed {
            tactic: "omega".to_string(),
            reason: "no direct Int reconstruction for goal".to_string(),
        });
    };
    state
        .close_goal(goal, proof)
        .map_err(|e| TacticError::ArithmeticFailed {
            tactic: "omega".to_string(),
            reason: format!("direct Int reconstruction rejected by close_goal: {e:?}"),
        })
}

/// `true` when `ty` is the `False` proposition.
fn is_false_target(ty: &Expr) -> bool {
    matches!(ty.kind(), clean_kernel::ExprKind::Const(n, _) if n.to_string() == "False")
}

/// Mathverse tactic for linear integer arithmetic.
///
/// Decides linear arithmetic goals over integers using a combination of
/// Fourier-Motzkin elimination and case splitting. This is more powerful
/// than `linarith` as it handles integer constraints with divisibility.
///
/// REQUIRES: `state` is a valid `ProofState` with at least one goal
/// REQUIRES: Goal involves integer linear arithmetic (equalities/inequalities/mod/div)
/// ENSURES: On `Ok(())`, the current goal is closed with a proof (certified or decide)
/// ENSURES: On `Err(NoGoals)`, `state.goals` was empty on entry
/// ENSURES: Tries `reduce_eq` first, then certified mathverse, then uncertified mathverse
/// ENSURES: Certified modular contradictions fail closed when replay cannot
///   construct a kernel-valid proof
///
/// # Algorithm
/// 1. Parse goal and hypotheses into linear constraints
/// 2. Apply Fourier-Motzkin elimination
/// 3. Handle integer constraints via branch and bound
/// 4. Check for contradiction
///
/// # Supported
/// - Linear inequalities: `a ≤ b`, `a < b`, `a ≥ b`, `a > b`
/// - Linear equalities: `a = b`
/// - Integer division: constraints involving `a / n`
/// - Modular arithmetic: constraints involving `a % n`
///
/// # Errors
/// - `NoGoals` if there are no goals
/// - `Other` if the goal cannot be decided
pub fn omega(state: &mut ProofState) -> TacticResult {
    if state.goals.is_empty() {
        return Err(TacticError::NoGoals);
    }

    // Pre-processing: normalize negated linear relations `¬(rel)` in both
    // hypothesis and goal position into their positive equivalents via
    // `push_neg` (`¬(a ≤ 2)` → `2 < a`, `¬(a ≥ 3)` goal → `a < 3`, etc.). This
    // is a proof-carrying rewrite: each rewrite is threaded through `propext` +
    // `Eq.subst` and re-checked by the kernel, so it only changes the *form* the
    // downstream solver sees, never soundness. After normalization the ordinary
    // `≤`/`<`/`=` solver + reconstruction handle the (now positive) relations.
    normalize_negated_relations(state);

    // Pre-processing: for equality goals, try reduce_eq first (#685).
    // Computational equality (delta/beta reduction) often suffices for goals
    // that mathverse would otherwise send to the constraint solver.
    if super::reduce_eq(state).is_ok() {
        return Ok(());
    }

    let goal = state.current_goal().ok_or(TacticError::NoGoals)?.clone();

    // Goal-driven direct Nat reconstruction (bounded slices A + B): proves the
    // `a ≤ a + b` non-negativity family and `n <|≤ c1 ⊢ n + k <|≤ c2` offset
    // family up front, since the certified FM would otherwise report `Sat`
    // (slice A: no `0 ≤ x` in the rational system) or fail the certificate
    // replay (slice B). The synthesized term is re-checked by `close_goal`, so
    // false goals (where the direct prover returns `None`) still fail closed.
    if try_direct_nat_reconstruction(state, &goal).is_ok() {
        return Ok(());
    }

    // Goal-driven direct Int reconstruction: linear Int equalities (`a + 0 = a`,
    // `a + b = b + a`, `-a + a = 0`), `a = b` from `Int` `≤`/`≥` bounds
    // (`Int.le_antisymm`), and `False` from contradictory `Int` equality
    // hypotheses (`a + b = 3, a + b = 5`). The Nat-specific paths above never
    // fire for these (`match_nat_eq` requires an `Eq` over `Nat`), so route Int
    // goals here first. Each synthesized term is re-checked by `close_goal`, so
    // false goals (where the Int prover returns `None`) still fail closed.
    if try_int_reconstruction(state, &goal).is_ok() {
        return Ok(());
    }

    // Try certified mathverse first for proof reconstruction
    if let Some((certified_constraints, hypothesis_fvars)) =
        extract_certified_mathverse_constraints(state, &goal)
    {
        match mathverse_check_certified(&certified_constraints) {
            MathverseCertifiedResult::Unsat(certificate) => {
                return close_certified_mathverse_contradiction(
                    state,
                    &goal,
                    &certificate,
                    &hypothesis_fvars,
                );
            }
            // Fall through to uncertified check
            MathverseCertifiedResult::Sat | MathverseCertifiedResult::Unknown => {}
        }
    }

    // Uncertified path: collect constraints and run Fourier-Motzkin
    mathverse_try_uncertified(state, &goal)
}

/// Uncertified mathverse path: collects constraints from hypotheses and goal,
/// runs Fourier-Motzkin, and falls back to linarith if needed.
///
/// Part of #2531: now tracks hypothesis fvars and attempts certified proof
/// reconstruction before failing closed or delegating to linarith.
///
/// REQUIRES: `state` has at least one goal; `goal` is the current goal
/// ENSURES: On `Ok(())`, goal is closed via certified proof, decide,
///   fail-closed certified replay, or linarith
/// ENSURES: Certified modular contradictions found here fail closed after
///   `decide` if no kernel proof is available
/// ENSURES: Parses hypotheses and goal with WHNF fallback (#685)
/// ENSURES: Falls back to `linarith` when mathverse FM check does not find Unsat
fn mathverse_try_uncertified(state: &mut ProofState, goal: &Goal) -> TacticResult {
    let mut constraints = Vec::new();
    let mut hypothesis_fvars: Vec<FVarId> = Vec::new();
    let whnf_fn: &dyn Fn(&Expr) -> Expr = &|e| state.whnf(goal, e);

    // First pass: collect raw constraints and hypothesis fvars to determine
    // the parseable hypothesis count before creating certificates (#2531).
    let mut raw_hyp_constraints: Vec<(OmegaConstraint, usize)> = Vec::new();
    for hyp in &goal.local_ctx {
        // Try parsing raw first; fall back to WHNF with sub-expression
        // normalization if needed (#685).
        let constraint = expr_to_mathverse_constraint(&hyp.ty, None).or_else(|| {
            let ty_whnf = state.whnf(goal, &hyp.ty);
            expr_to_mathverse_constraint(&ty_whnf, Some(whnf_fn))
        });
        if let Some(constraint) = constraint {
            let hyp_index = hypothesis_fvars.len();
            hypothesis_fvars.push(hyp.fvar);
            constraints.push(constraint.clone());
            raw_hyp_constraints.push((constraint, hyp_index));
        }
    }

    // Parse the goal and negate it to search for contradiction (WHNF fallback #685)
    let goal_constraint_opt = expr_to_mathverse_constraint(&goal.target, None).or_else(|| {
        let target_whnf = state.whnf(goal, &goal.target);
        expr_to_mathverse_constraint(&target_whnf, Some(whnf_fn))
    });
    let mut negated_goal: Option<OmegaConstraint> = None;
    if let Some(goal_constraint) = goal_constraint_opt {
        if let Some(negated) = negate_mathverse_constraint(&goal_constraint) {
            constraints.push(negated.clone());
            negated_goal = Some(negated);
        }
    }

    // Second pass: create certified constraints with correct dimension.
    // Must be done after first pass since from_hypothesis indexes into
    // a coefficient vector of size num_hyps.
    let num_hyps = hypothesis_fvars.len();
    let mut certified_constraints: Vec<CertifiedMathverseConstraint> = raw_hyp_constraints
        .into_iter()
        .map(|(c, idx)| CertifiedMathverseConstraint::from_hypothesis(c, idx, num_hyps))
        .collect();
    if let Some(neg_goal) = negated_goal {
        certified_constraints.push(CertifiedMathverseConstraint::from_negated_goal(
            neg_goal, num_hyps,
        ));
    }

    // Run the mathverse decision procedure (uncertified, for quick Sat/Unknown detection)
    if matches!(mathverse_check(&constraints), FMResult::Unsat) {
        // Part of #2531: attempt proof reconstruction via certified FM + build_mathverse_proof
        // before failing closed or delegating to linarith.
        if !certified_constraints.is_empty() {
            match mathverse_check_certified(&certified_constraints) {
                MathverseCertifiedResult::Unsat(certificate) => {
                    return close_certified_mathverse_contradiction(
                        state,
                        goal,
                        &certificate,
                        &hypothesis_fvars,
                    );
                }
                MathverseCertifiedResult::Sat | MathverseCertifiedResult::Unknown => {}
            }
        }

        if decide(state).is_ok() {
            return Ok(());
        }
        tracing::debug!(
            "mathverse: uncertified FM found contradiction but certified replay was unavailable; retrying linarith"
        );
    }

    // Brick 87: bounded Nat case-split disjunction goals — the everyday
    // `(h : n ≤ k) ⊢ n = 0 ∨ … ∨ n = k` family. A compound `Or` goal cannot
    // parse into a single constraint, so it was silently dropped from the
    // system above and this family ALWAYS fell through to the (failing)
    // linarith delegate. Detect the shape here — after every existing lane has
    // had its chance, so no previously-succeeding path changes — and prove it
    // with a closed interval-descent term re-checked by the kernel
    // (`close_goal` strict inference). Uncovered values and rejected
    // reconstructions FAIL LOUD with tactic "omega".
    // Bounded Nat truncated-subtraction lane: `(h : a ≤ b) ⊢ a - b = 0`. The
    // linear relaxation drops the `a - b` atom (truncation needs a case-split),
    // so this family always fell through to the failing linarith delegate. Fires
    // only on this exact shape with a matching hypothesis; the closed proof term
    // is re-checked by `close_goal`, so soundness never rests on detection.
    if let Some(result) = nat_sub::try_nat_sub_eq_zero(state, goal) {
        return result;
    }

    // Dual bounded Nat truncation shape: `(h : b ≤ a) ⊢ a - b + b = a`. Same
    // fail-closed, close_goal-rechecked design as the eq-zero lane above.
    if let Some(result) = nat_sub::try_nat_sub_add_cancel(state, goal) {
        return result;
    }

    // Add-commuted truncation shape: `(h : b ≤ a) ⊢ b + (a - b) = a`. The
    // `sub_add_cancel` lemma only spells the `(a - b) + b` orientation, so this
    // sibling commutes via `Nat.add_comm` and chains with `Eq.trans`. Same
    // fail-closed, close_goal-rechecked design.
    if let Some(result) = nat_sub::try_nat_add_sub_cancel(state, goal) {
        return result;
    }

    // Unconditional left-cancellation `⊢ (a + b) - a = b` — holds for all a, b
    // (no side condition), but the linear relaxation drops the `- a` atom.
    // `@Nat.ulpRound.add_sub_cancel_left a b` is re-checked by `close_goal`.
    if let Some(result) = nat_sub::try_nat_add_sub_cancel_left(state, goal) {
        return result;
    }

    // Bounded Nat modulo shape: `(h : 0 < k) ⊢ a % k < k`. The linear relaxation
    // drops the `a % k` atom (the mod bound needs the defining constraints), so
    // this fell through to the failing linarith delegate. Fires only on this
    // exact shape with a matching `0 < k` hypothesis; `@Nat.mod_lt a k h` is
    // re-checked by `close_goal`, so soundness never rests on detection.
    if let Some(result) = nat_div_mod::try_nat_mod_lt(state, goal) {
        return result;
    }

    // Euclidean division identity `⊢ (a / k) * k + a % k = a`. No side condition
    // (`Nat.div_add_mod` holds unconditionally); the mod/div atoms are dropped
    // by the linear relaxation. `@Nat.div_add_mod a k` is re-checked by
    // `close_goal`, so soundness never rests on detection.
    if let Some(result) = nat_div_mod::try_nat_div_add_mod(state, goal) {
        return result;
    }

    if let Some(result) = case_split::try_bounded_or_case_split(state, goal) {
        return result;
    }

    // Try linarith as fallback. Relabel its arithmetic failure so a failed
    // `by omega` names the tactic the user actually invoked: linarith is an
    // internal fallback here, and leaking its label as `tactic` misattributes
    // the failure. Every other error kind passes through unchanged.
    super::arith_linarith::linarith(state).map_err(|err| match err {
        TacticError::ArithmeticFailed { reason, .. } => TacticError::ArithmeticFailed {
            tactic: "omega".into(),
            reason: format!("(linarith fallback) {reason}"),
        },
        other => other,
    })
}

// =============================================================================
// Uncertified mathverse check
// =============================================================================

/// Run the mathverse decision procedure (uncertified path).
///
/// REQUIRES: Each element in `constraints` is a valid `OmegaConstraint`
/// ENSURES: `Unsat` implies the linear subset is truly unsatisfiable (sound)
/// ENSURES: `Unknown` when Ne/Mod/NotMod/LinearMod/NotLinearMod are present and
///   FM found Sat on the linear subset alone (#2146 soundness fix)
/// ENSURES: `Sat` only when no unsupported constraints were dropped and FM found Sat
/// ENSURES: Adding constraints only strengthens unsatisfiability: Unsat on linear
///   subset implies Unsat on the full system
///
/// # Soundness (#2146)
///
/// Previously returned `bool`, collapsing `Sat` and `Unknown` into `false`.
/// This silently dropped Ne/Mod constraints, making the uncertified path
/// report "satisfiable" (no contradiction) for problems where dropped
/// constraints actually create a contradiction. The fix returns `Unknown`
/// when unsupported constraints are present, so callers can fall through
/// to the certified path or linarith.
fn mathverse_check(constraints: &[OmegaConstraint]) -> FMResult {
    let mut linear_constraints = Vec::new();
    let mut has_unsupported = false;

    for c in constraints {
        match c {
            OmegaConstraint::Le(e) => {
                linear_constraints.push(LinearConstraint::Le(e.clone()));
            }
            OmegaConstraint::Lt(e) => {
                linear_constraints.push(LinearConstraint::Lt(e.clone()));
            }
            OmegaConstraint::Eq(e) => {
                linear_constraints.push(LinearConstraint::Eq(e.clone()));
            }
            // Ne/Mod variants cannot be represented as linear constraints.
            // Mark as unsupported so we return Unknown instead of silently
            // ignoring them (#2146).
            OmegaConstraint::Ne(_)
            | OmegaConstraint::Mod { .. }
            | OmegaConstraint::NotMod { .. }
            | OmegaConstraint::LinearMod { .. }
            | OmegaConstraint::NotLinearMod { .. } => {
                has_unsupported = true;
            }
        }
    }

    let fm_result = fourier_motzkin_check(&linear_constraints);

    // If FM found UNSAT using only the linear subset, the full system is
    // also UNSAT regardless of dropped constraints (adding constraints
    // only strengthens unsatisfiability).
    if matches!(fm_result, FMResult::Unsat) {
        return FMResult::Unsat;
    }

    // If unsupported constraints were dropped, we cannot trust a Sat result
    // — the dropped constraints might create a contradiction.
    if has_unsupported {
        return FMResult::Unknown;
    }

    fm_result
}
