// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certified mathverse constraint extraction and checking.
//!
//! Separates the certified path (with proof certificates) from the
//! uncertified mathverse check in `mod.rs`.

use clean_kernel::{Expr, FVarId};

use super::equality_solver::{solve_all_equalities, EqualityStepResult};
use super::gcd_normalize::{first_integer_infeasible, integer_normalize_eq, integer_tighten_le};
use super::le_solver::{solve_le_iteratively, LeSolverResult};
use super::{
    CertifiedMathverseConstraint, MathverseCertificate, MathverseCertifiedResult,
    MathverseContradictionType, OmegaConstraint,
};
use crate::tactic::arith_linarith::{
    fourier_motzkin_check_certified, CertifiedConstraint, FMCertifiedResult, LinarithCertificate,
};
use crate::tactic::arith_mathverse_parse::{
    expr_to_mathverse_constraint, negate_mathverse_constraint,
};
use crate::tactic::arith_mathverse_proof::{
    check_equality_contradictions, check_modular_contradictions,
};
use crate::tactic::arithmetic::{LinearConstraint, LinearExpr};
use crate::tactic::{Goal, ProofState};

/// Extract certified mathverse constraints from the proof state
///
/// REQUIRES: `state` is a valid `ProofState`; `goal` is the current goal
/// ENSURES: Returns `Some((constraints, fvars))` when at least one parseable constraint exists
/// ENSURES: Certificate dimension equals parseable hypothesis count (not total local_ctx size)
/// ENSURES: Each certificate tracks its originating hypothesis index or goal negation flag
/// ENSURES: Returns `None` when no constraints can be extracted
/// ENSURES: WHNF fallback (#685) is applied when raw parsing fails
pub(crate) fn extract_certified_mathverse_constraints(
    state: &ProofState,
    goal: &Goal,
) -> Option<(Vec<CertifiedMathverseConstraint>, Vec<FVarId>)> {
    let mut hypothesis_fvars: Vec<FVarId> = Vec::new();

    // First pass: collect raw constraints and hypothesis fvars to determine
    // the parseable hypothesis count before creating certificates.
    // Part of #2133 — certificate dimension fix (same pattern as linarith).
    let whnf_fn: &dyn Fn(&Expr) -> Expr = &|e| state.whnf(goal, e);
    let mut raw_constraints: Vec<(OmegaConstraint, usize)> = Vec::new();
    for decl in &goal.local_ctx {
        let ty = state.metas.instantiate(&decl.ty);
        // Try parsing the raw expression first; fall back to WHNF with
        // sub-expression normalization if needed (#685).
        let constraint = expr_to_mathverse_constraint(&ty, None).or_else(|| {
            let ty_whnf = state.whnf(goal, &decl.ty);
            expr_to_mathverse_constraint(&ty_whnf, Some(whnf_fn))
        });
        if let Some(c) = constraint {
            let hyp_index = hypothesis_fvars.len();
            hypothesis_fvars.push(decl.fvar);
            raw_constraints.push((c, hyp_index));
        }
    }

    // Certificate dimension: parseable hypothesis count only.
    // Mathverse tracks goal negation via uses_goal_negation flag, not a coefficient slot.
    let num_hyps = hypothesis_fvars.len();

    // Second pass: create certified constraints with uniform dimension
    let mut constraints: Vec<CertifiedMathverseConstraint> = raw_constraints
        .into_iter()
        .map(|(c, hyp_index)| CertifiedMathverseConstraint::from_hypothesis(c, hyp_index, num_hyps))
        .collect();

    // Add negation of goal (WHNF fallback on parse failure, #685)
    let target = state.metas.instantiate(&goal.target);
    let goal_constraint_opt = expr_to_mathverse_constraint(&target, None).or_else(|| {
        let target_whnf = state.whnf(goal, &goal.target);
        expr_to_mathverse_constraint(&target_whnf, Some(whnf_fn))
    });
    if let Some(goal_constraint) = goal_constraint_opt {
        if let Some(negated) = negate_mathverse_constraint(&goal_constraint) {
            constraints.push(CertifiedMathverseConstraint::from_negated_goal(
                negated, num_hyps,
            ));
        }
    }

    if constraints.is_empty() {
        return None;
    }

    // Inject the implicit `0 ≤ v` non-negativity bound that every Nat variable
    // carries. Without these, the rational/integer refutation treats a Nat
    // variable as ranging over all of ℤ, so a goal like `(h : a + 2 ≤ b) ⊢
    // b ≥ 2` looks satisfiable (`a = -3, b = -1`). Adding `0 ≤ v` for the Nat
    // atoms lets the Farkas/Fourier-Motzkin search find the genuine
    // contradiction `(b - a - 2 ≥ 0) + (a ≥ 0) ⊢ b - 2 ≥ 0`.
    //
    // Soundness: only Nat-typed local variables get the bound (it is *true* for
    // them), the synthetic constraints carry all-zero certificates so they never
    // change hypothesis attribution, and the reconstructed proof term is
    // kernel-rechecked. The final list is the existing constraints followed by
    // the synthetic non-negativity bounds for every Nat atom that appears.
    let nonneg = nat_nonneg_constraints(goal, &constraints, num_hyps);
    constraints.extend(nonneg);

    Some((constraints, hypothesis_fvars))
}

/// Collect the set of variable indices that (a) are Nat-typed local variables
/// and (b) appear in at least one already-collected linear constraint, and
/// return one synthetic `0 ≤ v` (`-v ≤ 0`) constraint per such variable.
///
/// A variable index here is `fvar.as_u64() as usize`, matching how
/// [`crate::tactic::arith_mathverse_parse::extract_single_var`] and `expr_to_linear`
/// encode free variables in [`LinearExpr`].
///
/// Soundness: `0 ≤ v` is unconditionally true for every Nat `v`, so adding it
/// can only *strengthen* unsatisfiability — never make a satisfiable system look
/// unsatisfiable. The constraints carry empty certificates.
fn nat_nonneg_constraints(
    goal: &Goal,
    constraints: &[CertifiedMathverseConstraint],
    num_hyps: usize,
) -> Vec<CertifiedMathverseConstraint> {
    use std::collections::BTreeSet;

    // Nat-typed local variables, keyed by their var index.
    let nat_vars: BTreeSet<usize> = goal
        .local_ctx
        .iter()
        .filter(|d| is_nat_type(&d.ty))
        .map(|d| d.fvar.as_u64() as usize)
        .collect();
    if nat_vars.is_empty() {
        return Vec::new();
    }

    // Variables that actually appear in some linear constraint already present.
    let mut appearing: BTreeSet<usize> = BTreeSet::new();
    for cc in constraints {
        if let Some(e) = constraint_linear_expr(&cc.constraint) {
            for &(v, _) in &e.coeffs {
                if nat_vars.contains(&v) {
                    appearing.insert(v);
                }
            }
        }
    }

    appearing
        .into_iter()
        .map(|v| {
            // `0 ≤ v` ⟺ `-v ≤ 0` ⟺ `Le(LinearExpr { coeffs: [(v, -1)], constant: 0 })`.
            let mut e = LinearExpr::var(v);
            e.coeffs[0].1 = -1;
            CertifiedMathverseConstraint::from_implicit_nonneg(OmegaConstraint::Le(e), num_hyps)
        })
        .collect()
}

/// Borrow the linear expression underlying the linear (`Le`/`Lt`/`Eq`/`Ne`)
/// variants of an `OmegaConstraint`. Modular variants return `None`.
fn constraint_linear_expr(c: &OmegaConstraint) -> Option<&LinearExpr> {
    match c {
        OmegaConstraint::Le(e)
        | OmegaConstraint::Lt(e)
        | OmegaConstraint::Eq(e)
        | OmegaConstraint::Ne(e)
        | OmegaConstraint::LinearMod { expr: e, .. }
        | OmegaConstraint::NotLinearMod { expr: e, .. } => Some(e),
        OmegaConstraint::Mod { .. } | OmegaConstraint::NotMod { .. } => None,
    }
}

/// `true` when `ty` is the `Nat` constant.
fn is_nat_type(ty: &Expr) -> bool {
    matches!(ty.kind(), clean_kernel::ExprKind::Const(n, _) if n.to_string() == "Nat")
}

/// Run certified mathverse check
///
/// REQUIRES: Each `CertifiedMathverseConstraint` has a well-formed certificate
/// ENSURES: `Unsat(cert)` implies the system is truly unsatisfiable and `cert` is a valid witness
/// ENSURES: Checks modular contradictions (parity, divisibility) before FM elimination
/// ENSURES: Checks Ne/Eq contradictions before FM elimination
/// ENSURES: Ne/Mod/NotMod constraints are filtered before FM (FM handles Le/Lt/Eq only)
/// ENSURES: `Sat`/`Unknown` propagated from certified Fourier-Motzkin
pub(crate) fn mathverse_check_certified(
    constraints: &[CertifiedMathverseConstraint],
) -> MathverseCertifiedResult {
    // Convert to linear constraints for Fourier-Motzkin
    let mut linear_constraints = Vec::new();
    let mut cert_map: Vec<MathverseCertificate> = Vec::new();

    for cc in constraints {
        match &cc.constraint {
            OmegaConstraint::Le(e) => {
                linear_constraints.push(LinearConstraint::Le(e.clone()));
                cert_map.push(cc.certificate.clone());
            }
            OmegaConstraint::Lt(e) => {
                linear_constraints.push(LinearConstraint::Lt(e.clone()));
                cert_map.push(cc.certificate.clone());
            }
            OmegaConstraint::Eq(e) => {
                linear_constraints.push(LinearConstraint::Eq(e.clone()));
                cert_map.push(cc.certificate.clone());
            }
            OmegaConstraint::Ne(e) => {
                // Handle disequality by checking for direct contradictions.
                // If we also have an Eq constraint for the same expression,
                // that's a direct contradiction.
                // Ne(e) means e ≠ 0, so if we have Eq(e) = 0, contradiction.
                // We track these for potential parity/divisibility proofs.
                linear_constraints.push(LinearConstraint::Ne(e.clone()));
                cert_map.push(cc.certificate.clone());
            }
            OmegaConstraint::Mod {
                var,
                remainder,
                modulus,
            } => {
                // Modular constraint: var ≡ remainder (mod modulus)
                // This means: ∃ k, var = modulus * k + remainder
                // We can encode this as bounds and use for parity detection:
                // - If modulus = 2 and remainder = 0, var is even
                // - If modulus = 2 and remainder = 1, var is odd
                // For general modular constraints, we check for contradictions
                // with other mod constraints on the same variable.

                // Track the modular constraint certificate
                let mut mod_cert = cc.certificate.clone();
                mod_cert.contradiction_type = if *modulus == 2 {
                    MathverseContradictionType::Parity
                } else {
                    MathverseContradictionType::Divisibility
                };
                cert_map.push(mod_cert);

                // Add a placeholder linear constraint (the var exists)
                // This helps track the variable in the system
                // Constraint: var - remainder ≡ 0 (mod modulus)
                let mut lin = LinearExpr::var(*var);
                lin.constant = -(*remainder);
                linear_constraints.push(LinearConstraint::Mod {
                    expr: lin,
                    modulus: *modulus,
                });
            }
            OmegaConstraint::NotMod { var, modulus } => {
                // Negated divisibility: ¬(m ∣ x) means x % m ≠ 0
                // This is the negation of x ≡ 0 (mod m)
                // For contradiction detection: if we have both x ≡ 0 (mod m)
                // and ¬(m ∣ x), that's a contradiction.

                // Track the certificate
                let mut mod_cert = cc.certificate.clone();
                mod_cert.contradiction_type = MathverseContradictionType::Divisibility;
                cert_map.push(mod_cert);

                // Add a NotMod linear constraint
                let lin = LinearExpr::var(*var);
                linear_constraints.push(LinearConstraint::NotMod {
                    expr: lin,
                    modulus: *modulus,
                });
            }
            OmegaConstraint::LinearMod {
                expr,
                remainder,
                modulus,
            } => {
                // Linear modular constraint: expr ≡ remainder (mod modulus)
                // e.g., (a + b) % 3 = 1 means a + b ≡ 1 (mod 3)
                // We encode this as: (expr - remainder) ≡ 0 (mod modulus)

                let mut mod_cert = cc.certificate.clone();
                mod_cert.contradiction_type = if *modulus == 2 {
                    MathverseContradictionType::Parity
                } else {
                    MathverseContradictionType::Divisibility
                };
                cert_map.push(mod_cert);

                // Constraint: expr - remainder ≡ 0 (mod modulus)
                let mut lin = expr.clone();
                lin.constant -= *remainder;
                linear_constraints.push(LinearConstraint::Mod {
                    expr: lin,
                    modulus: *modulus,
                });
            }
            OmegaConstraint::NotLinearMod {
                expr,
                remainder,
                modulus,
            } => {
                // Negated linear modular constraint: ¬(expr ≡ remainder (mod modulus))
                // e.g., (a + b) % 3 ≠ 1 means a + b ≢ 1 (mod 3)
                // We encode this as: (expr - remainder) % modulus ≠ 0

                let mut mod_cert = cc.certificate.clone();
                mod_cert.contradiction_type = MathverseContradictionType::Divisibility;
                cert_map.push(mod_cert);

                // Constraint: expr - remainder ≢ 0 (mod modulus)
                let mut lin = expr.clone();
                lin.constant -= *remainder;
                linear_constraints.push(LinearConstraint::NotMod {
                    expr: lin,
                    modulus: *modulus,
                });
            }
        }
    }

    // Integer-tighten Le constraints in place. `Σ aᵢxᵢ + c ≤ 0` becomes
    // `Σ (aᵢ/g)xᵢ + ⌈c/g⌉ ≤ 0` where g = gcd(aᵢ). Sound for ℤ; lets the
    // downstream Fourier-Motzkin pipeline see tighter bounds, which closes
    // some incompleteness gaps the fuzzer surfaced. Certificate map is
    // unchanged: the same hypothesis still contributes; we've just rewritten
    // its expression to the integer-tight equivalent.
    for c in linear_constraints.iter_mut() {
        if let Some(tightened) = integer_tighten_le(c) {
            *c = tightened;
        }
        if let Some(normalised) = integer_normalize_eq(c) {
            *c = normalised;
        }
    }

    // Full Lean-4-style equality elimination: alternate easy substitution
    // (`solveEasyEquality`, `Core.lean:316`) and bmod-reduction of hard
    // equalities (`dealWithHardEquality`, `Core.lean:340`). Substitution
    // propagates equalities into the rest of the system, exposing
    // contradictions for the downstream modular / GCD / FM checks.
    //
    // `next_var_index` starts one past the largest variable index in any
    // constraint; bmod adds fresh atoms beginning there.
    //
    // Sound: each rewriting step preserves the integer feasibility set
    // (linear back-substitution; bmod's `bmod_sat` lemma at
    // `Constraint.lean:383`). When the solver returns `Unsat` we
    // conservatively flag every contributing hypothesis (Arithmetic
    // contradiction type → falls back to `decide()` for kernel proof).
    let mut next_var_index = linear_constraints
        .iter()
        .flat_map(|c| c.expr().coeffs.iter().map(|&(v, _)| v))
        .max()
        .map_or(0, |m| m + 1);
    // Outer fixed-point loop mirroring Lean 4's `runMathverse`/`elimination`
    // cycle (`Core.lean:550–574`): alternate the equality solver with the
    // Le-only iterative solver until one of them concludes Unsat or
    // neither makes further progress. Each `NewEqualitiesEmitted` case
    // is when `solve_le_iteratively` detected opposing Le's like
    // `x ≤ 4 ∧ x ≥ 4` and promoted them to an equality — re-feeding it
    // to the equality solver propagates the now-pinned variable through
    // the rest of the system. Bounded by MAX_OUTER_ITERATIONS to avoid
    // pathological loops; soundness is preserved at every iteration.
    const MAX_OUTER_ITERATIONS: usize = 16;
    let mut solver_result = EqualityStepResult::NoEasyEqualities;
    for _ in 0..MAX_OUTER_ITERATIONS {
        let eq_result = solve_all_equalities(&mut linear_constraints, &mut next_var_index);
        if matches!(eq_result, EqualityStepResult::Unsat) {
            solver_result = eq_result;
            break;
        }
        for c in linear_constraints.iter_mut() {
            if let Some(tightened) = integer_tighten_le(c) {
                *c = tightened;
            }
            if let Some(normalised) = integer_normalize_eq(c) {
                *c = normalised;
            }
        }
        match solve_le_iteratively(&mut linear_constraints) {
            LeSolverResult::Unsat => {
                solver_result = EqualityStepResult::Unsat;
                break;
            }
            LeSolverResult::NewEqualitiesEmitted => continue,
            LeSolverResult::Unknown => {
                solver_result = eq_result;
                break;
            }
        }
    }

    if matches!(solver_result, EqualityStepResult::Unsat) {
        let mut coefficients = vec![0_i128; cert_map.first().map_or(0, |c| c.coefficients.len())];
        let mut uses_goal_negation = false;
        for cert in &cert_map {
            for (i, &c) in cert.coefficients.iter().enumerate() {
                if i < coefficients.len() && c != 0 {
                    coefficients[i] = 1;
                }
            }
            uses_goal_negation |= cert.uses_goal_negation;
        }
        return MathverseCertifiedResult::Unsat(MathverseCertificate {
            coefficients,
            uses_goal_negation,
            contradiction_type: MathverseContradictionType::Arithmetic,
        });
    }

    // Check for parity contradictions (x ≡ 0 (mod 2) and x ≡ 1 (mod 2))
    // and divisibility contradictions (conflicting residue classes)
    if let Some(cert) = check_modular_contradictions(&linear_constraints, &cert_map) {
        return MathverseCertifiedResult::Unsat(cert);
    }

    // Check for Ne/Eq contradictions (e = 0 and e ≠ 0)
    if let Some(cert) = check_equality_contradictions(&linear_constraints, &cert_map) {
        return MathverseCertifiedResult::Unsat(cert);
    }

    // Integer-tight refutation via GCD normalisation. Catches single-
    // constraint ℤ-Unsats that FM (which is rational) misses, e.g.
    // `2x = 1` or `3x + 6y ≡ 5 (mod m)`. Sound — the certificate is the
    // single contributing hypothesis with `MathverseContradictionType::Arithmetic`,
    // which falls back to `decide()` for kernel-proof reconstruction.
    if let Some(idx) = first_integer_infeasible(&linear_constraints) {
        let mut cert = cert_map[idx].clone();
        cert.contradiction_type = MathverseContradictionType::Arithmetic;
        return MathverseCertifiedResult::Unsat(cert);
    }

    // (Iterative Le solver already ran inside the outer loop above.)

    // Convert to certified linear constraints for linarith infrastructure
    // Filter out Ne and Mod constraints since Fourier-Motzkin doesn't handle them
    let certified_linear: Vec<CertifiedConstraint> = linear_constraints
        .iter()
        .zip(cert_map.iter())
        .filter_map(|(c, cert)| {
            match c {
                LinearConstraint::Le(_) | LinearConstraint::Lt(_) | LinearConstraint::Eq(_) => {
                    Some(CertifiedConstraint {
                        constraint: c.clone(),
                        certificate: LinarithCertificate {
                            coefficients: cert.coefficients.clone(),
                            result_constant: 1_i128, // Placeholder
                        },
                    })
                }
                LinearConstraint::Ne(_)
                | LinearConstraint::Mod { .. }
                | LinearConstraint::NotMod { .. } => None,
            }
        })
        .collect();

    // Use certified Fourier-Motzkin
    match fourier_motzkin_check_certified(&certified_linear) {
        FMCertifiedResult::Unsat(linarith_cert) => {
            MathverseCertifiedResult::Unsat(MathverseCertificate::from_linarith(&linarith_cert))
        }
        FMCertifiedResult::Sat => MathverseCertifiedResult::Sat,
        FMCertifiedResult::Unknown => MathverseCertifiedResult::Unknown,
    }
}
