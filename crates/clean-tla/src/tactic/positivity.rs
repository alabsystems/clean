// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Positivity proofs for TLA+ tactics.

use super::TlaTacticEngine;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Try to prove positivity: expr > 0 using hypotheses.
    ///
    /// For factorial_positive base case: fact(0) > 0
    /// 1. Look for hypothesis fact(0) = 1
    /// 2. Check 1 > 0 (always true for naturals)
    pub(super) fn try_positivity_with_hypotheses(
        &self,
        goal: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        // Extract comparison: lhs > 0 or lhs >= 1
        let (op, lhs, rhs) = self.extract_comparison(goal)?;

        // Handle n >= 0 for natural numbers (always true)
        if op == "TLA.ge" && self.is_zero(&rhs) {
            if self.trace {
                eprintln!(
                    "[TLA] positivity: {} >= 0 is trivially true for Nat",
                    self.expr_debug(&lhs)
                );
            }
            return Some(
                "{\"tactic\":\"positivity\",\"method\":\"nat_ge_zero\",\"status\":\"proved\"}"
                    .to_string(),
            );
        }

        // Check if it's a > 0 or >= 1 pattern
        let is_positivity_check =
            (op == "TLA.gt" && self.is_zero(&rhs)) || (op == "TLA.ge" && self.is_one(&rhs));

        if !is_positivity_check {
            return None;
        }

        if self.trace {
            eprintln!("[TLA] positivity: checking {} > 0", self.expr_debug(&lhs));
        }

        // First, try specialized hypotheses (for ForallIn quantifiers)
        let specialized = self.specialize_forall_hypotheses(hypotheses, &lhs);
        let all_hypotheses: Vec<_> = hypotheses.iter().cloned().chain(specialized).collect();

        // Look for hypothesis that gives lhs = something_positive
        for (i, hyp) in all_hypotheses.iter().enumerate() {
            if let Some((hyp_lhs, hyp_rhs)) = self.extract_equality(hyp) {
                // Normalize both sides
                let hyp_lhs_norm = self.normalize_arith(&hyp_lhs);
                let lhs_norm = self.normalize_arith(&lhs);

                if self.trace {
                    eprintln!(
                        "[TLA] positivity: checking hyp[{}]: {} = {}",
                        i,
                        self.expr_debug(&hyp_lhs_norm),
                        self.expr_debug(&hyp_rhs)
                    );
                }

                // Check if hypothesis LHS matches our goal LHS
                if self.exprs_equal(&hyp_lhs_norm, &lhs_norm) {
                    // Check if RHS is a positive constant
                    let hyp_rhs_norm = self.normalize_arith(&hyp_rhs);
                    if self.is_positive_constant(&hyp_rhs_norm) {
                        if self.trace {
                            eprintln!(
                                "[TLA] positivity: hyp[{}] gives {} = {} which is positive",
                                i,
                                self.expr_debug(&lhs),
                                self.expr_debug(&hyp_rhs_norm)
                            );
                        }
                        return Some(format!(
                            "{{\"tactic\":\"positivity\",\"hypothesis\":{},\"value\":\"{}\",\"status\":\"proved\"}}",
                            i,
                            self.expr_debug(&hyp_rhs_norm)
                        ));
                    }
                }
            }
        }

        // Check if lhs is directly a positive constant
        let lhs_norm = self.normalize_arith(&lhs);
        if self.is_positive_constant(&lhs_norm) {
            return Some(format!(
                "{{\"tactic\":\"positivity\",\"method\":\"direct\",\"value\":\"{}\",\"status\":\"proved\"}}",
                self.expr_debug(&lhs_norm)
            ));
        }

        // Check if lhs is succ(something) - always positive
        if self.is_succ_expr(&lhs_norm) {
            return Some(
                "{\"tactic\":\"positivity\",\"method\":\"succ\",\"status\":\"proved\"}".to_string(),
            );
        }

        // Check if lhs is n + k where k > 0 - always > 0 for n >= 0
        if self.is_add_positive(&lhs_norm) {
            return Some(
                "{\"tactic\":\"positivity\",\"method\":\"add_positive\",\"status\":\"proved\"}"
                    .to_string(),
            );
        }

        None
    }

    /// Try to prove step case positivity: IH: f(n) > 0 → f(succ n) > 0
    pub(super) fn try_positivity_step_case(
        &self,
        step_body: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        // Extract P(n) → P(succ n) structure
        let ExprKind::Pi(_, p_n, p_succ_n) = step_body.kind() else {
            return None;
        };

        // Both P(n) and P(succ n) should be positivity goals
        let (op_n, lhs_n, rhs_n) = self.extract_comparison(p_n)?;
        let (op_succ, lhs_succ, rhs_succ) = self.extract_comparison(p_succ_n)?;

        // Handle n >= 0 → succ(n) >= 0 pattern (always true for Nat)
        let is_nat_ge_zero_n = op_n == "TLA.ge" && self.is_zero(&rhs_n);
        let is_nat_ge_zero_succ = op_succ == "TLA.ge" && self.is_zero(&rhs_succ);

        if is_nat_ge_zero_n && is_nat_ge_zero_succ {
            if self.trace {
                eprintln!(
                    "[TLA] positivity_step: {} >= 0 → {} >= 0 (trivially true for Nat)",
                    self.expr_debug(&lhs_n),
                    self.expr_debug(&lhs_succ)
                );
            }
            return Some("{\"tactic\":\"positivity_step\",\"method\":\"nat_ge_zero_preservation\",\"status\":\"proved\"}".to_string());
        }

        // Handle n < n+1 → succ(n) < succ(n)+1 pattern
        let is_lt_plus_n =
            (op_n == "TLA.lt" || op_n == "TLA.le") && self.is_expr_plus_positive(&lhs_n, &rhs_n);
        let is_lt_plus_succ = (op_succ == "TLA.lt" || op_succ == "TLA.le")
            && self.is_expr_plus_positive(&lhs_succ, &rhs_succ);

        if is_lt_plus_n && is_lt_plus_succ && op_n == op_succ {
            if self.trace {
                eprintln!(
                    "[TLA] positivity_step: {} {} {} → {} {} {} (preserved under succ)",
                    self.expr_debug(&lhs_n),
                    op_n,
                    self.expr_debug(&rhs_n),
                    self.expr_debug(&lhs_succ),
                    op_succ,
                    self.expr_debug(&rhs_succ)
                );
            }
            return Some("{\"tactic\":\"positivity_step\",\"method\":\"lt_plus_preservation\",\"status\":\"proved\"}".to_string());
        }

        // Both should be > 0 or >= 1
        let is_positivity_n =
            (op_n == "TLA.gt" && self.is_zero(&rhs_n)) || (op_n == "TLA.ge" && self.is_one(&rhs_n));
        let is_positivity_succ = (op_succ == "TLA.gt" && self.is_zero(&rhs_succ))
            || (op_succ == "TLA.ge" && self.is_one(&rhs_succ));

        if !is_positivity_n || !is_positivity_succ {
            return None;
        }

        if self.trace {
            eprintln!(
                "[TLA] positivity_step: checking {} > 0 → {} > 0",
                self.expr_debug(&lhs_n),
                self.expr_debug(&lhs_succ)
            );
        }

        // Handle (n + k) > 0 → (succ(n) + k) > 0 pattern
        if self.is_add_positive(&lhs_n) && self.is_add_positive(&lhs_succ) {
            if self.trace {
                eprintln!(
                    "[TLA] positivity_step: {} > 0 → {} > 0 (both are add_positive)",
                    self.expr_debug(&lhs_n),
                    self.expr_debug(&lhs_succ)
                );
            }
            return Some("{\"tactic\":\"positivity_step\",\"method\":\"add_positive_preservation\",\"status\":\"proved\"}".to_string());
        }

        // Specialize hypotheses for the step case
        let specialized = self.specialize_forall_hypotheses(hypotheses, &lhs_succ);
        let all_hypotheses: Vec<_> = hypotheses.iter().cloned().chain(specialized).collect();

        // Look for recursive definition hypothesis
        for (i, hyp) in all_hypotheses.iter().enumerate() {
            if let Some(rewrite) = self.extract_recursive_definition(hyp) {
                // Check if this applies to lhs_succ (e.g., fact(succ n))
                if let Some(rewritten) = self.apply_recursive_rewrite(&lhs_succ, &rewrite) {
                    if self.trace {
                        eprintln!(
                            "[TLA] positivity_step: rewritten {} to {}",
                            self.expr_debug(&lhs_succ),
                            self.expr_debug(&rewritten)
                        );
                    }

                    // For factorial: rewritten = (n+1) * fact(n)
                    if self.is_product_of_positives(&rewritten, &lhs_n) {
                        if self.trace {
                            eprintln!(
                                "[TLA] positivity_step: {} is product of positives",
                                self.expr_debug(&rewritten)
                            );
                        }
                        return Some(format!(
                            "{{\"tactic\":\"positivity_step\",\"hypothesis\":{},\"method\":\"product_positive\",\"status\":\"proved\"}}",
                            i
                        ));
                    }
                }
            }
        }

        None
    }

    /// Check if expr is a product where both factors are positive.
    ///
    /// `ih_term` is the term we know is positive from the induction hypothesis.
    pub(super) fn is_product_of_positives(&self, expr: &Expr, ih_term: &Expr) -> bool {
        // Check for multiplication: App(App(TLA.mul, a), b)
        if let Some((op, a, b)) = self.extract_binary_arith(expr) {
            if op == "TLA.mul" || op == "Nat.mul" || op == "Mul.mul" {
                // Check if one factor is the IH term
                let a_is_ih = self.exprs_equal(&a, ih_term);
                let b_is_ih = self.exprs_equal(&b, ih_term);

                if self.trace {
                    eprintln!(
                        "[TLA] is_product_of_positives: {} * {}, a_is_ih={}, b_is_ih={}",
                        self.expr_debug(&a),
                        self.expr_debug(&b),
                        a_is_ih,
                        b_is_ih
                    );
                }

                if a_is_ih {
                    // b should be positive
                    let b_norm = self.normalize_arith(&b);
                    if self.is_positive_constant(&b_norm) || self.is_succ_expr(&b_norm) {
                        return true;
                    }
                    if let Some(_inner) = self.extract_succ_arg(&b) {
                        return true;
                    }
                }

                if b_is_ih {
                    // a should be positive
                    let a_norm = self.normalize_arith(&a);
                    if self.is_positive_constant(&a_norm) || self.is_succ_expr(&a_norm) {
                        return true;
                    }
                    if let Some(_inner) = self.extract_succ_arg(&a) {
                        return true;
                    }
                }
            }
        }

        false
    }
}
