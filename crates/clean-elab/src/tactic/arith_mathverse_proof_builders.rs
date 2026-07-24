// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse proof term builders for parity and divisibility contradictions.
//!
//! Split from `arith_mathverse_proof.rs` (#307). These functions build kernel-valid
//! proof terms when the mathverse procedure finds parity or divisibility contradictions.

use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, FVarId, Level};

use super::arith_mathverse_parse::expr_to_mathverse_constraint;
use super::omega_tactic::{MathverseCertificate, OmegaConstraint};
use super::{Goal, ProofState};

fn instantiated_local_decl_ty(state: &ProofState, goal: &Goal, fvar: FVarId) -> Option<Expr> {
    goal.local_ctx
        .iter()
        .find(|decl| decl.fvar == fvar)
        .map(|decl| state.metas.instantiate(&decl.ty))
}

fn extract_parity_subject(expr: &Expr) -> Option<Expr> {
    match expr.kind() {
        clean_kernel::ExprKind::App(f, arg) => {
            if let clean_kernel::ExprKind::Const(name, _) = f.kind() {
                let name_str = name.to_string();
                if matches!(name_str.as_str(), "Even" | "Odd" | "Nat.Even" | "Nat.Odd") {
                    return Some(arg.as_ref().clone());
                }
            }

            if let clean_kernel::ExprKind::App(f2, _arg2) = f.kind() {
                if let clean_kernel::ExprKind::App(f3, _inst) = f2.kind() {
                    if let clean_kernel::ExprKind::App(f4, _ty) = f3.kind() {
                        if let clean_kernel::ExprKind::Const(name, _) = f4.kind() {
                            let name_str = name.to_string();
                            if matches!(name_str.as_str(), "Even" | "Odd") {
                                return Some(arg.as_ref().clone());
                            }
                        }
                    }
                }
            }

            None
        }
        _ => None,
    }
}

/// Build a proof from a parity contradiction (even = odd)
///
/// When we have constraints like:
/// - x ≡ 0 (mod 2) meaning x is even
/// - x ≡ 1 (mod 2) meaning x is odd
///
/// These are contradictory. The proof is reconstructed only when the
/// environment explicitly provides a theorem bridge for the accepted parity
/// hypothesis surface.
///
/// REQUIRES: `hypothesis_fvars` is non-empty
/// REQUIRES: `certificate.contradiction_type` is `Parity`
/// REQUIRES: certificate has at least 2 active hypotheses with conflicting parity
/// ENSURES: On Some, returns a proof term of type `False`
/// ENSURES: On None, caller should fall back to decide/sorry
pub(crate) fn build_parity_contradiction_proof(
    state: &ProofState,
    goal: &Goal,
    certificate: &MathverseCertificate,
    hypothesis_fvars: &[FVarId],
    env: &Environment,
) -> Option<Expr> {
    // For parity contradictions, we need to find the hypotheses that establish
    // conflicting parity and combine them to derive False.
    //
    // The proof structure is:
    // 1. From h1 : x ≡ 0 (mod 2), we have ∃ k, x = 2k (Even x)
    // 2. From h2 : x ≡ 1 (mod 2), we have ∃ k, x = 2k + 1 (Odd x)
    // 3. These are contradictory
    //
    // We use: Nat.even_and_odd_elim n h_even h_odd : False when available.

    if hypothesis_fvars.is_empty() {
        return None;
    }

    // Find the two hypotheses with non-zero coefficients (the conflicting ones)
    let active: Vec<usize> = certificate
        .coefficients
        .iter()
        .enumerate()
        .filter(|&(_, &c)| c > 0)
        .map(|(i, _)| i)
        .collect();

    // We expect exactly 2 hypotheses for a parity contradiction
    if active.len() < 2 {
        // If we don't have 2 active hypotheses, fall back to placeholder
        return None;
    }

    // Identify which active hypotheses correspond to Even and Odd constraints
    let mut even_idx: Option<usize> = None;
    let mut odd_idx: Option<usize> = None;
    let mut parity_subject: Option<Expr> = None;

    for idx in active {
        if idx >= hypothesis_fvars.len() {
            continue;
        }

        let fvar = hypothesis_fvars[idx];
        let hyp_ty = instantiated_local_decl_ty(state, goal, fvar);

        if let Some(ty) = hyp_ty {
            if let Some(c) = expr_to_mathverse_constraint(&ty, None) {
                match c {
                    OmegaConstraint::Mod {
                        modulus, remainder, ..
                    } if modulus == 2 && remainder == 0 => {
                        if parity_subject.is_none() {
                            parity_subject = extract_parity_subject(&ty);
                        }
                        if even_idx.is_none() {
                            even_idx = Some(idx);
                        }
                    }
                    OmegaConstraint::Mod {
                        modulus, remainder, ..
                    } if modulus == 2 && remainder == 1 => {
                        if parity_subject.is_none() {
                            parity_subject = extract_parity_subject(&ty);
                        }
                        if odd_idx.is_none() {
                            odd_idx = Some(idx);
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    let (Some(even_idx), Some(odd_idx)) = (even_idx, odd_idx) else {
        return None;
    };

    if even_idx >= hypothesis_fvars.len() || odd_idx >= hypothesis_fvars.len() {
        return None;
    }

    let h_even = Expr::fvar(hypothesis_fvars[even_idx]);
    let h_odd = Expr::fvar(hypothesis_fvars[odd_idx]);
    let parity_subject = parity_subject?;

    // Use a theorem-backed eliminator only when the environment provides it.
    let even_odd_elim = Name::from_string("Nat.even_and_odd_elim");
    if env.get_const(&even_odd_elim).is_some() {
        let elim = Expr::const_(even_odd_elim, vec![]);
        return Some(Expr::apps(elim, [parity_subject, h_even, h_odd]));
    }

    // No explicit proof bridge exists for this parity contradiction surface.
    None
}

/// Build a proof from a divisibility contradiction
///
/// When we have constraints like:
/// - n | k (n divides k) meaning k ≡ 0 (mod n)
/// - n ∤ k (n does not divide k) meaning k % n ≠ 0
///
/// Or more generally, conflicting modular constraints:
/// - x ≡ r₁ (mod m)
/// - x ≡ r₂ (mod m) where r₁ ≠ r₂ and 0 ≤ r₁, r₂ < m
///
/// The proof uses the certificate to identify which hypotheses establish
/// the contradiction, then builds a proof term using:
/// - `absurd` when we have `h : m ∣ n` and `h' : ¬(m ∣ n)`
/// - `Nat.mod_contradiction` for conflicting residue classes
///
/// REQUIRES: `hypothesis_fvars` is non-empty
/// REQUIRES: `certificate.contradiction_type` is `Divisibility`
/// REQUIRES: certificate has at least 2 active hypotheses with conflicting modular constraints
/// ENSURES: On Some, returns a proof term of type `False`
/// ENSURES: On None, caller should fall back to decide/sorry
pub(crate) fn build_divisibility_contradiction_proof(
    state: &ProofState,
    goal: &Goal,
    certificate: &MathverseCertificate,
    hypothesis_fvars: &[FVarId],
    env: &Environment,
) -> Option<Expr> {
    // For divisibility contradictions, we prove that conflicting residue classes
    // cannot both hold for the same value.
    //
    // Case 1: h1 : m ∣ n and h2 : ¬(m ∣ n)
    //   Use: absurd h1 h2 : False
    //
    // Case 2: h1 : x ≡ r₁ (mod m) and h2 : x ≡ r₂ (mod m) with r₁ ≠ r₂
    //   From h1: x = m*k₁ + r₁
    //   From h2: x = m*k₂ + r₂
    //   So: m*(k₁ - k₂) = r₂ - r₁
    //   If |r₂ - r₁| < m and r₁ ≠ r₂, this is impossible

    if hypothesis_fvars.is_empty() {
        return None;
    }

    // Find the hypotheses with non-zero coefficients
    let active: Vec<usize> = certificate
        .coefficients
        .iter()
        .enumerate()
        .filter(|&(_, &c)| c > 0)
        .map(|(i, _)| i)
        .collect();

    // We expect at least 2 hypotheses for a divisibility contradiction
    if active.len() < 2 {
        return None;
    }

    // Collect modular constraints for active hypotheses so we can pair the right ones.
    let mut mod_constraints: Vec<(usize, i64, i64)> = Vec::new(); // (idx, remainder, modulus)
    let mut not_mod_constraints: Vec<(usize, i64, i64)> = Vec::new(); // (idx, remainder, modulus)

    for idx in active {
        if idx >= hypothesis_fvars.len() {
            continue;
        }

        let fvar = hypothesis_fvars[idx];
        let hyp_ty = instantiated_local_decl_ty(state, goal, fvar);

        if let Some(ty) = hyp_ty {
            if let Some(constraint) = expr_to_mathverse_constraint(&ty, None) {
                match constraint {
                    OmegaConstraint::Mod {
                        remainder, modulus, ..
                    }
                    | OmegaConstraint::LinearMod {
                        remainder, modulus, ..
                    } => mod_constraints.push((idx, remainder, modulus)),
                    OmegaConstraint::NotMod { modulus, .. } => {
                        not_mod_constraints.push((idx, 0, modulus));
                    }
                    OmegaConstraint::NotLinearMod {
                        remainder, modulus, ..
                    } => not_mod_constraints.push((idx, remainder, modulus)),
                    _ => {}
                }
            }
        }
    }

    // Case 1: Direct Mod / NotMod contradiction with the same modulus and remainder
    // This handles both r=0 (divisibility) and r≠0 (general modular) cases
    //   h1 : x ≡ r (mod m)   (i.e., x % m = r)
    //   h2 : x % m ≠ r       (NotMod/NotLinearMod with remainder r)
    // Use: absurd h1 h2 : False
    let absurd_name = Name::from_string("absurd");
    if env.get_const(&absurd_name).is_some() {
        for (mod_idx, remainder, modulus) in &mod_constraints {
            for (not_idx, not_remainder, not_modulus) in &not_mod_constraints {
                // Match when same expression has: x ≡ r (mod m) AND x % m ≠ r
                if *not_remainder == *remainder && modulus == not_modulus {
                    if *mod_idx >= hypothesis_fvars.len() || *not_idx >= hypothesis_fvars.len() {
                        continue;
                    }
                    let h_mod_fvar = hypothesis_fvars[*mod_idx];
                    let h_not_mod_fvar = hypothesis_fvars[*not_idx];
                    let target_prop = instantiated_local_decl_ty(state, goal, h_mod_fvar)?;
                    let h_mod = Expr::fvar(h_mod_fvar);
                    let h_not_mod = Expr::fvar(h_not_mod_fvar);
                    let false_ty = Expr::const_(Name::from_string("False"), vec![]);
                    let absurd = Expr::const_(absurd_name.clone(), vec![Level::zero()]);
                    return Some(Expr::apps(
                        absurd,
                        [target_prop, false_ty, h_mod, h_not_mod],
                    ));
                }
            }
        }
    }

    // Case 2: Conflicting modular constraints (different remainders)
    // h1 : x % m = r₁  AND  h2 : x % m = r₂  where r₁ ≠ r₂
    //
    // Proof strategy:
    //   From h1: x % m = r1 and h2: x % m = r2
    //   We derive r1 = r2 via:  Eq.trans (Eq.symm h1) h2
    //   When r1 ≠ r2 are distinct literals, (r1 = r2) is decidably False.
    //
    // Using Nat.noConfusion:
    //   h_eq : r1 = r2  derived from Eq.trans (Eq.symm h1) h2
    //   Nat.noConfusion h_eq : False  (when r1 ≠ r2 are distinct Nat literals)
    build_conflicting_remainder_proof(&mod_constraints, hypothesis_fvars, env)
}

/// Build proof for Case 2: conflicting modular remainders (r₁ ≠ r₂).
///
/// REQUIRES: `mod_constraints` has at least two entries with the same modulus but different remainders
/// ENSURES: On Some, returns a proof of `False` via `Eq.trans` + `Nat.noConfusion`
fn build_conflicting_remainder_proof(
    mod_constraints: &[(usize, i64, i64)],
    hypothesis_fvars: &[FVarId],
    env: &Environment,
) -> Option<Expr> {
    let eq_symm_name = Name::from_string("Eq.symm");
    let eq_trans_name = Name::from_string("Eq.trans");
    let nat_noconfusion_name = Name::from_string("Nat.noConfusion");

    let have_eq_trans = env.get_const(&eq_trans_name).is_some();
    let have_eq_symm = env.get_const(&eq_symm_name).is_some();
    // Nat.noConfusion is stored as a recursor, not a constant
    let have_nat_noconfusion = env.get_const(&nat_noconfusion_name).is_some()
        || env.get_recursor(&nat_noconfusion_name).is_some();

    if !(have_eq_trans && have_eq_symm && have_nat_noconfusion) {
        return None;
    }

    for (i, &(idx_i, remainder_i, modulus_i)) in mod_constraints.iter().enumerate() {
        for &(idx_j, remainder_j, modulus_j) in mod_constraints.iter().skip(i + 1) {
            // Check if same modulus but different remainders
            if modulus_i == modulus_j && remainder_i != remainder_j {
                if idx_i >= hypothesis_fvars.len() || idx_j >= hypothesis_fvars.len() {
                    continue;
                }

                // h1 : x % m = r1   and   h2 : x % m = r2
                let h1 = Expr::fvar(hypothesis_fvars[idx_i]);
                let h2 = Expr::fvar(hypothesis_fvars[idx_j]);

                // Build r1 and r2 as Nat literals
                let r1 = Expr::nat_lit(remainder_i as u64);
                let r2 = Expr::nat_lit(remainder_j as u64);

                // We need the common "middle" term: x % m
                // For h1 : x % m = r1, we need Eq.symm h1 : r1 = x % m
                // Then Eq.trans (Eq.symm h1) h2 : r1 = r2
                //
                // Eq.symm : {α : Sort u} → {a b : α} → a = b → b = a
                // Eq.trans : {α : Sort u} → {a b c : α} → a = b → b = c → a = c

                // Build Eq.symm {Nat} {x % m} {r1} h1
                // This gives us: r1 = x % m
                let eq_symm = Expr::const_(eq_symm_name.clone(), vec![Level::Param(Name::anon())]);
                // Need to extract the middle term from the hypothesis type
                // For now, we use placeholders via implicit args
                // Eq.symm with implicits: {α} {a} {b} (h : a = b) : b = a
                let symm_h1 = Expr::app(eq_symm, h1.clone());

                // Build Eq.trans {Nat} {r1} {x % m} {r2} (Eq.symm h1) h2
                // This gives us: r1 = r2
                let eq_trans =
                    Expr::const_(eq_trans_name.clone(), vec![Level::Param(Name::anon())]);
                let trans_proof = Expr::app(Expr::app(eq_trans, symm_h1), h2.clone());

                // Build Nat.noConfusion {False} {r1} {r2} trans_proof
                // Nat.noConfusion : {P : Sort u} → {v1 v2 : Nat} → v1 = v2 → Nat.noConfusionType P v1 v2
                // When v1 ≠ v2 definitionally, noConfusionType P v1 v2 = P
                // So Nat.noConfusion h : False  when h : r1 = r2 and r1 ≠ r2
                let false_ty = Expr::const_(Name::from_string("False"), vec![]);
                // Universe zero correct: Nat.noConfusion targets False (Prop)
                let nat_nc = Expr::const_(nat_noconfusion_name.clone(), vec![Level::zero()]);
                // Apply: {P := False} {v1 := r1} {v2 := r2} trans_proof
                let proof = Expr::app(
                    Expr::app(Expr::app(Expr::app(nat_nc, false_ty), r1), r2),
                    trans_proof,
                );

                return Some(proof);
            }
        }
    }

    // Fall back: return None to trigger decide/sorry fallback
    None
}
