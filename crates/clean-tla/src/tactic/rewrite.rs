// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rewriting methods for TLA+ tactics — hypothesis-based step case proofs.

use super::{RecursiveRewrite, TlaTacticEngine};
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Try to prove step case using hypothesis substitution.
    pub(super) fn try_step_case_with_hypotheses(
        &self,
        step_body: &Expr,
        _body: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        // Extract P(n) → P(succ n) structure
        let ExprKind::Pi(_, p_n, p_succ_n) = step_body.kind() else {
            return None;
        };

        // Extract equalities from P(n) and P(succ n)
        let Some((ih_lhs, ih_rhs)) = self.extract_equality(p_n) else {
            if self.trace {
                eprintln!("[TLA] step_hyp: P(n) is not an equality");
            }
            return None;
        };
        let Some((goal_lhs, goal_rhs)) = self.extract_equality(p_succ_n) else {
            if self.trace {
                eprintln!("[TLA] step_hyp: P(succ n) is not an equality");
            }
            return None;
        };

        if self.trace {
            eprintln!(
                "[TLA] step_hyp: IH: {} = {}",
                self.expr_debug(&ih_lhs),
                self.expr_debug(&ih_rhs)
            );
            eprintln!(
                "[TLA] step_hyp: goal: {} = {}",
                self.expr_debug(&goal_lhs),
                self.expr_debug(&goal_rhs)
            );
        }

        // Look for a recursive definition hypothesis
        for (i, hyp) in hypotheses.iter().enumerate() {
            if let Some(rewrite) = self.extract_recursive_definition(hyp) {
                if self.trace {
                    eprintln!(
                        "[TLA] step_hyp: found recursive def in hyp[{}]: {} applied to (x+1) = {}",
                        i,
                        rewrite.func_name,
                        self.expr_debug(&rewrite.rhs_template)
                    );
                }

                // Try to apply this rewrite to the goal LHS
                if let Some(rewritten_lhs) = self.apply_recursive_rewrite(&goal_lhs, &rewrite) {
                    if self.trace {
                        eprintln!(
                            "[TLA] step_hyp: rewritten LHS: {}",
                            self.expr_debug(&rewritten_lhs)
                        );
                    }

                    // Normalize LHS first
                    let lhs_expanded = self.normalize_arith(&rewritten_lhs);

                    if self.trace {
                        eprintln!(
                            "[TLA] step_hyp: expanded LHS: {}",
                            self.expr_debug(&lhs_expanded)
                        );
                    }

                    // Normalize IH pattern too
                    let ih_lhs_norm = self.normalize_arith(&ih_lhs);
                    let ih_rhs_norm = self.normalize_arith(&ih_rhs);

                    // Now substitute the IH: replace ih_lhs with ih_rhs
                    let substituted = self.substitute_ih(&lhs_expanded, &ih_lhs_norm, &ih_rhs_norm);

                    if self.trace {
                        eprintln!(
                            "[TLA] step_hyp: after IH substitution: {}",
                            self.expr_debug(&substituted)
                        );
                    }

                    // Normalize again after substitution
                    let lhs_norm = self.normalize_arith(&substituted);
                    let rhs_norm = self.normalize_arith(&goal_rhs);

                    if self.trace {
                        eprintln!(
                            "[TLA] step_hyp: normalized LHS: {}",
                            self.expr_debug(&lhs_norm)
                        );
                        eprintln!(
                            "[TLA] step_hyp: normalized RHS: {}",
                            self.expr_debug(&rhs_norm)
                        );
                    }

                    // Check if they're equal after normalization. SOUNDNESS:
                    // this `exprs_equal` on the fully-normalized, IH-substituted
                    // LHS vs RHS is the ONLY accepting path. The former
                    // `verify_sum_formula_step` fallback was removed: it
                    // shape-matched `(_/2)+_` against `(_/2)` and returned true
                    // while discarding both numerators, so it accepted a false
                    // closed form (`sum(n) = (n*(n+3))/2` against the recursive
                    // hyps whose true closed form is `n*(n+1)/2`). When the
                    // sound normalization check below fails, fall through to a
                    // real prover (fail-closed) rather than a shape guess.
                    if self.exprs_equal(&lhs_norm, &rhs_norm) {
                        return Some(format!(
                            "{{\"tactic\":\"step_hyp\",\"hypothesis\":{},\"method\":\"recursive_rewrite\",\"status\":\"proved\"}}",
                            i
                        ));
                    }
                }
            }
        }

        None
    }

    /// Extract a recursive definition from a hypothesis.
    ///
    /// Looks for pattern: ∀k ∈ Nat. f(k+1) = <expr involving f(k)>
    pub(super) fn extract_recursive_definition(&self, hyp: &Expr) -> Option<RecursiveRewrite> {
        // Unwrap TLA.forallIn Nat (λk. ...)
        let Some((_set, _var, body)) = self.extract_tla_forall_in(hyp) else {
            // Try Pi form: Π k : Nat, ...
            if let ExprKind::Pi(_, ty, inner_body) = hyp.kind() {
                if self.is_nat_type(ty) {
                    return self.extract_recursive_def_from_equality(inner_body);
                }
            }
            return None;
        };

        // body should be an equality: f(k+1) = ...
        self.extract_recursive_def_from_equality(&body)
    }

    /// Extract recursive definition from an equality expression.
    fn extract_recursive_def_from_equality(&self, body: &Expr) -> Option<RecursiveRewrite> {
        let (lhs, rhs) = self.extract_equality(body)?;
        self.extract_recursive_pattern(&lhs, rhs)
    }

    /// Extract recursive pattern from an application expression.
    /// Handles multi-arg functions like pow(n, k+1).
    fn extract_recursive_pattern(&self, lhs: &Expr, rhs: Expr) -> Option<RecursiveRewrite> {
        // Collect all arguments by peeling applications
        let mut args = Vec::new();
        let mut current = lhs.clone();

        while let ExprKind::App(f, arg) = current.kind() {
            args.push(arg.as_ref().clone());
            current = f.as_ref().clone();
        }

        // Now current should be a Const (the function name)
        let ExprKind::Const(func_name, _) = current.kind() else {
            return None;
        };

        // args are in reverse order (rightmost first)
        if args.is_empty() {
            return None;
        }

        let last_arg = &args[0];
        if !self.is_succ_of_bvar0(last_arg) {
            return None;
        }

        // Prefix args are all except the last (and in original order)
        let mut prefix_args: Vec<_> = args[1..].to_vec();
        prefix_args.reverse();

        Some(RecursiveRewrite {
            func_name: func_name.to_string(),
            prefix_args,
            rhs_template: rhs,
        })
    }

    /// Apply a recursive rewrite to an expression.
    pub(super) fn apply_recursive_rewrite(
        &self,
        expr: &Expr,
        rewrite: &RecursiveRewrite,
    ) -> Option<Expr> {
        // Try to match the expression against the rewrite pattern
        if let Some(result) = self.try_match_and_rewrite(expr, rewrite) {
            return Some(result);
        }

        // Not a direct match - try to rewrite in subexpressions
        if let ExprKind::App(f, arg) = expr.kind() {
            if let Some(new_f) = self.apply_recursive_rewrite(f, rewrite) {
                return Some(Expr::app(new_f, arg.as_ref().clone()));
            }
            if let Some(new_arg) = self.apply_recursive_rewrite(arg, rewrite) {
                return Some(Expr::app(f.as_ref().clone(), new_arg));
            }
        }
        None
    }

    /// Try to match expr against a recursive rewrite pattern and apply it.
    fn try_match_and_rewrite(&self, expr: &Expr, rewrite: &RecursiveRewrite) -> Option<Expr> {
        // Peel off applications to get function and args
        let mut args = Vec::new();
        let mut current = expr.clone();

        while let ExprKind::App(f, arg) = current.kind() {
            args.push(arg.as_ref().clone());
            current = f.as_ref().clone();
        }

        // Check function name matches
        let ExprKind::Const(func_name, _) = current.kind() else {
            return None;
        };
        if func_name.to_string() != rewrite.func_name {
            return None;
        }

        // args are in reverse order
        let expected_args = rewrite.prefix_args.len() + 1;
        if args.len() != expected_args {
            return None;
        }

        // Check prefix args match
        let actual_prefix: Vec<_> = args[1..].iter().rev().cloned().collect();
        for (expected, actual) in rewrite.prefix_args.iter().zip(actual_prefix.iter()) {
            if !self.exprs_equal(expected, actual) {
                return None;
            }
        }

        // Check last arg is succ(something) or (something + 1)
        let last_arg = &args[0];
        let inner = self.extract_succ_arg(last_arg)?;

        // Substitute BVar(0) in rhs_template with 'inner'
        let result = rewrite.rhs_template.instantiate(&inner);
        Some(result)
    }

    /// Substitute occurrences of pattern with replacement in expr.
    pub(super) fn substitute_ih(&self, expr: &Expr, pattern: &Expr, replacement: &Expr) -> Expr {
        // Check if this expression matches the pattern
        if self.exprs_equal(expr, pattern) {
            return replacement.clone();
        }

        // Recursively substitute in subexpressions
        match expr.kind() {
            ExprKind::App(f, a) => {
                let f_sub = self.substitute_ih(f, pattern, replacement);
                let a_sub = self.substitute_ih(a, pattern, replacement);
                Expr::app(f_sub, a_sub)
            }
            ExprKind::Lam(info, ty, body) => {
                let ty_sub = self.substitute_ih(ty, pattern, replacement);
                let body_sub = self.substitute_ih(body, pattern, replacement);
                Expr::lam(*info, ty_sub, body_sub)
            }
            ExprKind::Pi(info, ty, body) => {
                let ty_sub = self.substitute_ih(ty, pattern, replacement);
                let body_sub = self.substitute_ih(body, pattern, replacement);
                Expr::pi(*info, ty_sub, body_sub)
            }
            _ => expr.clone(),
        }
    }

    /// Create a multiplication expression: a * b using TLA.mul
    pub(super) fn make_mul(&self, a: &Expr, b: &Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("TLA.mul"), vec![]),
                a.clone(),
            ),
            b.clone(),
        )
    }

    /// Create an addition expression: a + b using TLA.add
    pub(super) fn make_add(&self, a: &Expr, b: &Expr) -> Expr {
        use clean_kernel::name::Name;
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("TLA.add"), vec![]),
                a.clone(),
            ),
            b.clone(),
        )
    }
}
