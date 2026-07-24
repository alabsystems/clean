// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tseitin clausification rule handlers for ay proof reconstruction.
//!
//! Premiseless tautology clauses emitted by ay's Boolean encoder:
//! - `or_pos` / `or_neg`: Or-chain Tseitin encoding
//! - `and_pos` / `and_neg`: And-chain Tseitin encoding
//! - `equiv_pos1/2` / `equiv_neg1/2`: Equivalence Tseitin encoding (in `tseitin_equiv.rs`)

use ay_core::{ProofId, TermId};
use clean_kernel::Expr;

use super::{ReconstructResult, ReconstructionContext, ReconstructionError};
use crate::bridge::disjunction;

impl<'a> ReconstructionContext<'a> {
    /// Reconstruct an or_pos Tseitin tautology clause.
    ///
    /// or_pos clause: `{¬Q, l₁, ..., lₙ}` where `Q = l₁ ∨ ... ∨ lₙ`.
    ///
    /// Proof: `Classical.em Q : Or Q (Q → False)`, then `Or.rec` swap to get
    /// `Or (Q → False) Q`. Uses the Pi form `Q → False` (not `Not Q`) to match
    /// the syntactic type of `Classical.em` and avoid definitional unfolding
    /// during kernel type-checking.
    pub(super) fn reconstruct_or_pos(
        &mut self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if clause.len() < 2 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "or_pos clause must have at least 2 literals".to_string(),
            });
        }
        let clause_props = self.translate_clause_props(clause)?;
        // Q = the disjunction of the positive literals (everything after ¬Q)
        let q = disjunction::or_chain_type(&clause_props[1..]);
        // Use Q → False (Pi form) instead of Not Q to match Classical.em's type exactly.
        // Classical.em Q : Or Q (Q → False), so mk_or_swap needs b = Q → False.
        let not_q_pi = Expr::pi(
            clean_kernel::expr::BinderInfo::Default,
            q.clone(),
            Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]),
        );
        let em = disjunction::mk_classical_em(&q);
        Ok(disjunction::mk_or_swap(&q, &not_q_pi, &em))
    }

    /// Reconstruct an or_neg Tseitin tautology clause.
    ///
    /// or_neg clause: `{Q, ¬lᵢ}` where `Q = l₁ ∨ ... ∨ lₙ` and `lᵢ` is
    /// a sub-disjunct of Q.
    ///
    /// Proof: `Classical.em lᵢ : Or lᵢ (lᵢ → False)`, then:
    /// - Case `h : lᵢ` → inject h at position i into the Or chain Q → `Or.inl`
    /// - Case `h : ¬lᵢ` → `Or.inr Q ¬lᵢ h`
    pub(super) fn reconstruct_or_neg(
        &mut self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if clause.len() != 2 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "or_neg clause must have exactly 2 literals, got {}",
                    clause.len()
                ),
            });
        }
        let trace = self
            .trace
            .as_ref()
            .ok_or(ReconstructionError::ProofNotAvailable)?;

        // clause[0] = Q (the source disjunction), clause[1] = ¬lᵢ
        let q_term = clause[0];
        let neg_li_term = clause[1];

        // Strip Not from ¬lᵢ to get lᵢ.
        let li_term = trace
            .as_not(neg_li_term)
            .ok_or(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "or_neg: second clause literal is not a negation".to_string(),
            })?;

        // Flatten Q to find the position of lᵢ.
        let q_disjuncts = trace.flatten_or(q_term);
        let position = q_disjuncts.iter().position(|&d| d == li_term).ok_or(
            ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: "or_neg: negated literal not found in source disjunction".to_string(),
            },
        )?;

        // Translate all sub-disjuncts to kernel propositions.
        let q_sub_props: Vec<Expr> = q_disjuncts
            .iter()
            .map(|&t| self.translate_term(t))
            .collect::<ReconstructResult<Vec<_>>>()?;

        let q_expr = disjunction::or_chain_type(&q_sub_props);
        let li_prop = q_sub_props[position].clone();

        // ¬lᵢ as Pi form: lᵢ → False
        let false_expr = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
        let not_li_pi = Expr::pi(
            clean_kernel::expr::BinderInfo::Default,
            li_prop.clone(),
            false_expr,
        );

        // Target clause type: Or Q (¬lᵢ)
        let clause_type = Expr::app(
            Expr::app(
                Expr::const_(clean_kernel::name::Name::from_string("Or"), vec![]),
                q_expr.clone(),
            ),
            not_li_pi.clone(),
        );

        // Classical.em lᵢ : Or lᵢ (lᵢ → False)
        let em = disjunction::mk_classical_em(&li_prop);

        // Build Or.rec on the em proof:
        // Case h : lᵢ → inject into Q at position, then Or.inl
        // Case h : ¬lᵢ → Or.inr
        let motive = disjunction::mk_constant_or_motive(&li_prop, &not_li_pi, &clause_type);

        // f_inl: fun (h : lᵢ) => Or.inl Q (¬lᵢ) (inject h at position in Q)
        let inject_h_in_q =
            disjunction::inject_into_or_chain(&q_sub_props, position, Expr::bvar(0));
        let f_inl = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            li_prop.clone(),
            disjunction::mk_or_inl(&q_expr, &not_li_pi, &inject_h_in_q),
        );

        // f_inr: fun (h : ¬lᵢ) => Or.inr Q (¬lᵢ) h
        let f_inr = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            not_li_pi.clone(),
            disjunction::mk_or_inr(&q_expr, &not_li_pi, &Expr::bvar(0)),
        );

        Ok(disjunction::mk_or_rec(
            &li_prop, &not_li_pi, &motive, &f_inl, &f_inr, &em,
        ))
    }

    /// Reconstruct an and_pos Tseitin tautology clause.
    ///
    /// and_pos(i) clause: `{¬(and a₁...aₙ), aᵢ}` — if the conjunction holds
    /// then the i-th conjunct holds.
    ///
    /// Proof: `Classical.em (And a₁ (...))`, then:
    /// - Case `h : And a₁ (...)` → extract conjunct i via And.left/And.right → Or.inr
    /// - Case `h : (And ...) → False` → Or.inl (def-eq to Not (And ...))
    pub(super) fn reconstruct_and_pos(
        &mut self,
        i: u32,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if clause.len() != 2 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "and_pos clause must have exactly 2 literals, got {}",
                    clause.len()
                ),
            });
        }
        let trace = self
            .trace
            .as_ref()
            .ok_or(ReconstructionError::ProofNotAvailable)?;

        // clause[0] = not(and_term), clause[1] = aᵢ
        let and_term =
            trace
                .as_not(clause[0])
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "and_pos: first clause literal is not a negation".to_string(),
                })?;
        let conjunct_terms =
            trace
                .as_and(and_term)
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "and_pos: negated literal is not an And application".to_string(),
                })?;
        let n = conjunct_terms.len();
        if (i as usize) >= n {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!("and_pos({i}): index out of bounds for {n}-ary And"),
            });
        }
        // Copy conjunct TermIds before translating (borrows trace immutably).
        let conjunct_terms_owned: Vec<_> = conjunct_terms.to_vec();

        // Translate clause props and all conjuncts.
        let clause_props = self.translate_clause_props(clause)?;
        let conjunct_props: Vec<Expr> = conjunct_terms_owned
            .iter()
            .map(|&t| self.translate_term(t))
            .collect::<ReconstructResult<Vec<_>>>()?;

        let and_type = disjunction::and_chain_type(&conjunct_props);

        // Not (And ...) in Pi form for Classical.em.
        let false_expr = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
        let not_and_pi = Expr::pi(
            clean_kernel::expr::BinderInfo::Default,
            and_type.clone(),
            false_expr,
        );

        // Classical.em (And ...) : Or (And ...) ((And ...) → False)
        let em = disjunction::mk_classical_em(&and_type);

        let clause_type = disjunction::or_chain_type(&clause_props);
        let motive = disjunction::mk_constant_or_motive(&and_type, &not_and_pi, &clause_type);

        // f_inl: fun (h : And ...) => Or.inr (extract_conjunct h i n)
        let extracted = disjunction::extract_and_conjunct(&Expr::bvar(0), i as usize, n);
        let f_inl = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            and_type.clone(),
            disjunction::inject_into_or_chain(&clause_props, 1, extracted),
        );

        // f_inr: fun (h : ¬And) => Or.inl h
        let f_inr = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            not_and_pi.clone(),
            disjunction::inject_into_or_chain(&clause_props, 0, Expr::bvar(0)),
        );

        Ok(disjunction::mk_or_rec(
            &and_type,
            &not_and_pi,
            &motive,
            &f_inl,
            &f_inr,
            &em,
        ))
    }

    /// Reconstruct an and_neg Tseitin tautology clause.
    ///
    /// and_neg clause: `{¬a₁, ..., ¬aₙ, (and a₁...aₙ)}` — if all conjuncts
    /// hold then the conjunction holds.
    ///
    /// Proof: nested `Classical.em` on each conjunct. If all hold, build an
    /// `And.intro` chain and inject at the last position. If any negation holds,
    /// inject at that negation's position in the Or chain.
    pub(super) fn reconstruct_and_neg(
        &mut self,
        clause: &[TermId],
        step_id: ProofId,
    ) -> ReconstructResult<Expr> {
        if clause.len() < 3 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "and_neg clause must have at least 3 literals, got {}",
                    clause.len()
                ),
            });
        }
        let trace = self
            .trace
            .as_ref()
            .ok_or(ReconstructionError::ProofNotAvailable)?;

        // clause = [¬a₁, ..., ¬aₙ, and_term] — the And is the last element.
        let and_term = *clause.last().expect("invariant: clause.len() >= 3");
        let conjunct_terms =
            trace
                .as_and(and_term)
                .ok_or_else(|| ReconstructionError::UnsupportedStep {
                    step_index: step_id.0,
                    description: "and_neg: last clause literal is not an And application"
                        .to_string(),
                })?;
        let n = conjunct_terms.len();
        if clause.len() != n + 1 {
            return Err(ReconstructionError::UnsupportedStep {
                step_index: step_id.0,
                description: format!(
                    "and_neg: clause has {} literals but And has {} conjuncts",
                    clause.len(),
                    n
                ),
            });
        }
        let conjunct_terms_owned: Vec<_> = conjunct_terms.to_vec();

        // Translate clause and conjuncts.
        let clause_props = self.translate_clause_props(clause)?;
        let conjunct_props: Vec<Expr> = conjunct_terms_owned
            .iter()
            .map(|&t| self.translate_term(t))
            .collect::<ReconstructResult<Vec<_>>>()?;

        let clause_type = disjunction::or_chain_type(&clause_props);

        // Build nested Classical.em proof.
        let proof = Self::build_and_neg_nested_em(&conjunct_props, &clause_props, &clause_type, 0);
        Ok(proof)
    }

    /// Build the nested Classical.em proof for and_neg.
    ///
    /// At each level, case-splits on conjunct[level]:
    /// - inl (conjunct holds): recurse to case-split the next conjunct
    /// - inr (negation holds): inject negation proof at position `level` in clause
    ///
    /// Base case (all conjuncts hold): build And.intro chain from bvar references,
    /// inject at position `n` (the And term's position at the end of the clause).
    fn build_and_neg_nested_em(
        conjuncts: &[Expr],
        clause_props: &[Expr],
        clause_type: &Expr,
        level: usize,
    ) -> Expr {
        let n = conjuncts.len();

        if level == n {
            // Base case: all conjuncts hold as bvar(n-1-i) for conjunct i.
            let and_proof = disjunction::build_and_chain_from_bvars(conjuncts, 0, n);
            // Inject at position n (the And term is the last clause element).
            return disjunction::inject_into_or_chain(clause_props, n, and_proof);
        }

        // Classical.em on conjuncts[level]
        let a = &conjuncts[level];
        let false_expr = Expr::const_(clean_kernel::name::Name::from_string("False"), vec![]);
        let not_a_pi = Expr::pi(
            clean_kernel::expr::BinderInfo::Default,
            a.clone(),
            false_expr,
        );

        let em = disjunction::mk_classical_em(a);
        let motive = disjunction::mk_constant_or_motive(a, &not_a_pi, clause_type);

        // f_inl: fun (h : a) => <recurse with level+1>
        let f_inl = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            a.clone(),
            Self::build_and_neg_nested_em(conjuncts, clause_props, clause_type, level + 1),
        );

        // f_inr: fun (h : ¬a) => inject at position `level` in clause
        let f_inr = Expr::lam(
            clean_kernel::expr::BinderInfo::Default,
            not_a_pi.clone(),
            disjunction::inject_into_or_chain(clause_props, level, Expr::bvar(0)),
        );

        disjunction::mk_or_rec(a, &not_a_pi, &motive, &f_inl, &f_inr, &em)
    }

    // NOTE: reconstruct_equiv_tautology moved to tseitin_equiv.rs
    // for file size compliance. The method is defined as an impl on
    // ReconstructionContext in that file.
}
