// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Superposition inference rules: generating inferences from clause pairs.
//!
//! Implements the four core inference rules of the superposition calculus:
//! - **Superposition**: Rewrites terms using equations from other clauses
//! - **Equality Resolution**: Resolves reflexive disequalities
//! - **Equality Factoring**: Factors equal positive literals
//! - **Rewrite Literal**: Helper for position-based term rewriting

use super::{unify, Clause, Inference, Literal, Position, Substitution, SuperpositionProver, Term};

impl SuperpositionProver {
    /// Generate new clauses by inference rules
    pub(super) fn generate_clauses(&mut self, given: &Clause) -> Vec<Clause> {
        let mut result = Vec::new();

        // Temporarily take the processed set to avoid cloning it (O(1) swap
        // instead of the previous O(N) clone). `superposition` only reads
        // its two clause arguments and mutates `self.next_id`/`self.ordering`,
        // so the empty `self.processed` is not observed during the loop.
        let processed_clauses = std::mem::take(&mut self.processed);

        // Superposition with processed clauses
        for processed in &processed_clauses {
            // Superposition: given into processed
            result.extend(self.superposition(given, processed));
            // Superposition: processed into given
            result.extend(self.superposition(processed, given));
        }

        // Restore the processed set before continuing
        self.processed = processed_clauses;

        // Self-superposition
        result.extend(self.superposition(given, given));

        // Equality resolution
        result.extend(self.equality_resolution(given));

        // Equality factoring
        result.extend(self.equality_factoring(given));

        self.stats.inferences += result.len() as u64;
        result
    }

    /// Rewrite one side of a literal at a position, applying full MGU (#2276).
    /// Returns `None` if `replace_at` fails — the inference is skipped rather
    /// than producing an unsound clause from a full-substitution fallback (#2274).
    pub(super) fn rewrite_literal(
        lit: &Literal,
        is_lhs: bool,
        path: &[usize],
        replacement: Term,
        mgu: &Substitution,
    ) -> Option<Literal> {
        if is_lhs {
            let new_lhs = lit.lhs.replace_at_path(path, replacement)?.apply_subst(mgu);
            Some(Literal {
                lhs: new_lhs,
                rhs: lit.rhs.apply_subst(mgu),
                positive: lit.positive,
            })
        } else {
            let new_rhs = lit.rhs.replace_at_path(path, replacement)?.apply_subst(mgu);
            Some(Literal {
                lhs: lit.lhs.apply_subst(mgu),
                rhs: new_rhs,
                positive: lit.positive,
            })
        }
    }

    /// Superposition inference: rewrite c2 using equations from c1
    pub(super) fn superposition(&mut self, c1: &Clause, c2: &Clause) -> Vec<Clause> {
        let mut result = Vec::new();

        // Rename variables in c2 to avoid conflicts
        let max_var = c1.vars().into_iter().max().unwrap_or(0);
        let c2_renamed = c2.rename_vars(max_var + 1);

        // For each positive equation l=r in c1
        for (i, lit1) in c1.positive_literals() {
            // Try l=r and r=l
            for (big, small) in [(&lit1.lhs, &lit1.rhs), (&lit1.rhs, &lit1.lhs)] {
                // Skip if big is a variable (no superposition into variables)
                if big.is_var() {
                    continue;
                }

                // For each literal in c2_renamed
                for (j, lit2) in c2_renamed.literals.iter().enumerate() {
                    for (is_lhs, target_term) in [(true, &lit2.lhs), (false, &lit2.rhs)] {
                        target_term.visit_positions(|path, subterm| {
                            // Skip variable positions
                            if subterm.is_var() {
                                return;
                            }

                            // Try to unify big with subterm
                            if let Some(mgu) = unify(big, subterm) {
                                // Check ordering constraints
                                let big_sigma = big.apply_subst(&mgu);
                                let small_sigma = small.apply_subst(&mgu);

                                if !self.ordering.greater_equal(&big_sigma, &small_sigma) {
                                    return;
                                }

                                // Skip inference if replace_at fails (#2274)
                                let Some(new_lit) =
                                    Self::rewrite_literal(lit2, is_lhs, path, small_sigma, &mgu)
                                else {
                                    return;
                                };

                                // Build result clause: remaining c1 + c2 lits + rewritten lit
                                let mut lits: Vec<Literal> = c1
                                    .literals
                                    .iter()
                                    .enumerate()
                                    .filter(|(k, _)| *k != i)
                                    .chain(
                                        c2_renamed
                                            .literals
                                            .iter()
                                            .enumerate()
                                            .filter(|(k, _)| *k != j),
                                    )
                                    .map(|(_, l)| l.apply_subst(&mgu))
                                    .collect();
                                lits.push(new_lit);
                                let id = self.next_id;
                                self.next_id += 1;
                                result.push(Clause {
                                    literals: lits,
                                    id,
                                    parents: vec![c1.id, c2.id],
                                    inference: Inference::Superposition(
                                        c1.id,
                                        c2.id,
                                        Position(path.to_vec()),
                                    ),
                                });
                            }
                        });
                    }
                }
            }
        }

        result
    }

    /// Equality resolution: from s ≠ t ∨ C, derive Cσ where σ = mgu(s, t)
    pub(super) fn equality_resolution(&mut self, clause: &Clause) -> Vec<Clause> {
        let mut result = Vec::new();

        for (i, lit) in clause.negative_literals() {
            if let Some(mgu) = unify(&lit.lhs, &lit.rhs) {
                let mut new_literals = Vec::new();
                for (j, l) in clause.literals.iter().enumerate() {
                    if j != i {
                        new_literals.push(l.apply_subst(&mgu));
                    }
                }

                let new_clause = Clause {
                    literals: new_literals,
                    id: self.next_id,
                    parents: vec![clause.id],
                    inference: Inference::EqualityResolution(clause.id),
                };
                self.next_id += 1;

                result.push(new_clause);
            }
        }

        result
    }

    /// Equality factoring: from s = t ∨ s' = t' ∨ C, derive (s = t ∨ t ≠ t' ∨ C)σ
    /// where σ = mgu(s, s') and tσ is not greater than sσ
    pub(super) fn equality_factoring(&mut self, clause: &Clause) -> Vec<Clause> {
        let mut result = Vec::new();
        let positive: Vec<_> = clause.positive_literals();

        for (idx1, (i, lit1)) in positive.iter().enumerate() {
            for &(i2, lit2) in positive.iter().skip(idx1 + 1) {
                // Try to unify the left-hand sides
                if let Some(mgu) = unify(&lit1.lhs, &lit2.lhs) {
                    let s_sigma = lit1.lhs.apply_subst(&mgu);
                    let t_sigma = lit1.rhs.apply_subst(&mgu);

                    // Check ordering constraint: t ≤ s
                    if self.ordering.greater(&t_sigma, &s_sigma) {
                        continue;
                    }

                    let mut new_literals = Vec::new();

                    // Keep first equation
                    new_literals.push(lit1.apply_subst(&mgu));

                    // Add disequation t ≠ t'
                    new_literals.push(Literal::neq(t_sigma, lit2.rhs.apply_subst(&mgu)));

                    // Add remaining literals (exclude only the two factored literals)
                    for (j, l) in clause.literals.iter().enumerate() {
                        if j != *i && j != i2 {
                            new_literals.push(l.apply_subst(&mgu));
                        }
                    }

                    let new_clause = Clause {
                        literals: new_literals,
                        id: self.next_id,
                        parents: vec![clause.id],
                        inference: Inference::EqualityFactoring(clause.id),
                    };
                    self.next_id += 1;

                    result.push(new_clause);
                }
            }
        }

        result
    }
}
