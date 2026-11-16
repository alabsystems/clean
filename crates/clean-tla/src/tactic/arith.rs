// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic simplification tactics for TLA+.

use super::TlaTacticEngine;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Try to prove an equality by arithmetic simplification.
    pub(super) fn try_arith_simplify(&self, goal: &Expr) -> Option<String> {
        // Extract equality: Eq A lhs rhs or TLA.eq lhs rhs
        let (lhs, rhs) = self.extract_equality(goal)?;

        if self.trace {
            eprintln!(
                "[TLA] arith_simplify: checking {} = {}",
                self.expr_debug(&lhs),
                self.expr_debug(&rhs)
            );
        }

        // Normalize both sides and check if they become equal
        let lhs_norm = self.normalize_arith(&lhs);
        let rhs_norm = self.normalize_arith(&rhs);

        if self.exprs_equal(&lhs_norm, &rhs_norm) {
            if self.trace {
                eprintln!("[TLA] arith_simplify: normalized to equal expressions");
            }
            return Some(
                "{\"tactic\":\"arith_simplify\",\"method\":\"normalize\",\"status\":\"proved\"}"
                    .to_string(),
            );
        }

        // Try identity-specific rules
        if let Some(rule) = self.check_arith_identity(&lhs, &rhs) {
            if self.trace {
                eprintln!("[TLA] arith_simplify: applied rule {}", rule);
            }
            return Some(format!(
                "{{\"tactic\":\"arith_simplify\",\"rule\":\"{}\",\"status\":\"proved\"}}",
                rule
            ));
        }

        // Try polynomial normalization (ring) for algebraic equality.
        // SOUNDNESS: `expr_to_polynomial` returns `None` when the polynomial
        // form is undecided (coefficient overflow, or a subtraction node). A
        // `None` side must NOT be treated as equal — only accept when both
        // sides canonicalize to `Some` identical polynomials. This rejects the
        // overflow-collision false proof `3037000500² = 4000000000²` and the
        // truncated-subtraction false proof `(2-5)+5 = 2`.
        if let (Some(lhs_poly), Some(rhs_poly)) =
            (self.expr_to_polynomial(&lhs), self.expr_to_polynomial(&rhs))
        {
            if lhs_poly == rhs_poly {
                if self.trace {
                    eprintln!("[TLA] arith_simplify: ring proved via polynomial equality");
                }
                return Some(
                    "{\"tactic\":\"arith_simplify\",\"method\":\"ring\",\"status\":\"proved\"}"
                        .to_string(),
                );
            }
        }

        None
    }

    /// Normalize arithmetic expression by applying identity rules
    pub(super) fn normalize_arith(&self, expr: &Expr) -> Expr {
        use clean_kernel::name::Name;

        // First: normalize numeric representations
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Int.ofNat" || s == "TLA.int" {
                    if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = arg.kind() {
                        if n.to_u64() == Some(0) {
                            return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                        }
                        if n.to_u64() == Some(1) {
                            return Expr::app(
                                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                                Expr::const_(Name::from_string("Nat.zero"), vec![]),
                            );
                        }
                        return Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
                            n.clone(),
                        )));
                    }
                }
            }
        }

        // Pattern: App(App(TLA.op, a), b) for binary ops
        if let ExprKind::App(f, b) = expr.kind() {
            if let ExprKind::App(op_with_a, a) = f.kind() {
                if let ExprKind::Const(op_name, levels) = op_with_a.kind() {
                    let op_str = op_name.to_string();

                    // Recursively normalize operands
                    let a_norm = self.normalize_arith(a);
                    let b_norm = self.normalize_arith(b);

                    // Apply identity rules
                    match op_str.as_str() {
                        "TLA.add" | "Nat.add" | "Add.add" => {
                            if self.is_zero(&b_norm) {
                                return a_norm;
                            }
                            if self.is_zero(&a_norm) {
                                return b_norm;
                            }
                        }
                        "TLA.mul" | "Nat.mul" | "Mul.mul" => {
                            if self.is_zero(&b_norm) {
                                return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                            }
                            if self.is_zero(&a_norm) {
                                return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                            }
                            if self.is_one(&b_norm) {
                                return a_norm;
                            }
                            if self.is_one(&a_norm) {
                                return b_norm;
                            }
                            // Left distributivity: k * (a + b) → k*a + k*b
                            if let Some((inner_op, c, d)) = self.extract_binary_arith(&b_norm) {
                                if inner_op == "TLA.add"
                                    || inner_op == "Nat.add"
                                    || inner_op == "Add.add"
                                {
                                    let k_times_c = self.make_mul(&a_norm, &c);
                                    let k_times_d = self.make_mul(&a_norm, &d);
                                    let result = self.make_add(&k_times_c, &k_times_d);
                                    return self.normalize_arith(&result);
                                }
                            }
                            // Handle k * succ(n) → k*n + k
                            if let Some(inner) = self.extract_succ(&b_norm) {
                                let k_times_inner = self.make_mul(&a_norm, &inner);
                                let result = self.make_add(&k_times_inner, &a_norm);
                                return self.normalize_arith(&result);
                            }
                            // Right distributivity: (a + b) * k → a*k + b*k
                            if let Some((inner_op, c, d)) = self.extract_binary_arith(&a_norm) {
                                if inner_op == "TLA.add"
                                    || inner_op == "Nat.add"
                                    || inner_op == "Add.add"
                                {
                                    let c_times_k = self.make_mul(&c, &b_norm);
                                    let d_times_k = self.make_mul(&d, &b_norm);
                                    let result = self.make_add(&c_times_k, &d_times_k);
                                    return self.normalize_arith(&result);
                                }
                            }
                            // Handle succ(n) * k → n*k + k
                            if let Some(inner) = self.extract_succ(&a_norm) {
                                let inner_times_k = self.make_mul(&inner, &b_norm);
                                let result = self.make_add(&inner_times_k, &b_norm);
                                return self.normalize_arith(&result);
                            }
                        }
                        "TLA.sub" | "Nat.sub" | "Sub.sub" if self.is_zero(&b_norm) => {
                            return a_norm;
                        }
                        "TLA.div" | "Nat.div" | "Div.div" => {
                            // SOUNDNESS: `0 / b = 0` is only valid when the
                            // divisor is provably nonzero. Division by 0 is
                            // unspecified in TLA+ (a CHOOSE value), so `0 / v`
                            // for a free `v` is NOT provably 0. Fire the
                            // `0/b → 0` rewrite only under a discharged b≠0
                            // side-condition; otherwise leave the term intact
                            // so no spurious equality is manufactured.
                            if self.is_zero(&a_norm) && self.is_provably_nonzero(&b_norm) {
                                return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                            }
                            // `a / 1 = a` is always sound (divisor is 1 ≠ 0).
                            if self.is_one(&b_norm) {
                                return a_norm;
                            }
                        }
                        "TLA.mod" | "Nat.mod" | "Mod.mod" => {
                            // SOUNDNESS: same definedness guard as div — `0 % b`
                            // and `a % 1` are only 0 when the divisor is nonzero.
                            if self.is_zero(&a_norm) && self.is_provably_nonzero(&b_norm) {
                                return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                            }
                            // `a % 1 = 0` is always sound (divisor is 1 ≠ 0).
                            if self.is_one(&b_norm) {
                                return Expr::const_(Name::from_string("Nat.zero"), vec![]);
                            }
                        }
                        _ => {}
                    }

                    // Rebuild with normalized operands
                    return Expr::app(
                        Expr::app(
                            Expr::from_kind(ExprKind::Const(op_name.clone(), levels.clone())),
                            a_norm,
                        ),
                        b_norm,
                    );
                }
            }
        }

        // Fallback: for any App not handled above, recursively normalize subexpressions
        if let ExprKind::App(f, arg) = expr.kind() {
            let f_norm = self.normalize_arith(f);
            let arg_norm = self.normalize_arith(arg);
            if !self.exprs_equal(&f_norm, f) || !self.exprs_equal(&arg_norm, arg) {
                return Expr::app(f_norm, arg_norm);
            }
        }

        // No simplification - return as-is
        expr.clone()
    }

    /// Check if an equality matches a known arithmetic identity
    pub(super) fn check_arith_identity(&self, lhs: &Expr, rhs: &Expr) -> Option<&'static str> {
        // x + 0 = x
        if let Some((op, a, b)) = self.extract_binary_arith(lhs) {
            if (op == "TLA.add" || op == "Nat.add") && self.is_zero(&b) && self.exprs_equal(&a, rhs)
            {
                return Some("add_zero_right");
            }
            if (op == "TLA.add" || op == "Nat.add") && self.is_zero(&a) && self.exprs_equal(&b, rhs)
            {
                return Some("add_zero_left");
            }
            if (op == "TLA.mul" || op == "Nat.mul") && self.is_one(&b) && self.exprs_equal(&a, rhs)
            {
                return Some("mul_one_right");
            }
            if (op == "TLA.mul" || op == "Nat.mul") && self.is_one(&a) && self.exprs_equal(&b, rhs)
            {
                return Some("mul_one_left");
            }
            if (op == "TLA.mul" || op == "Nat.mul") && self.is_zero(&b) && self.is_zero(rhs) {
                return Some("mul_zero_right");
            }
            if (op == "TLA.mul" || op == "Nat.mul") && self.is_zero(&a) && self.is_zero(rhs) {
                return Some("mul_zero_left");
            }
            if (op == "TLA.sub" || op == "Nat.sub") && self.is_zero(&b) && self.exprs_equal(&a, rhs)
            {
                return Some("sub_zero");
            }
        }

        // Also check reversed: rhs op = lhs
        if let Some((op, a, b)) = self.extract_binary_arith(rhs) {
            if (op == "TLA.add" || op == "Nat.add") && self.is_zero(&b) && self.exprs_equal(&a, lhs)
            {
                return Some("add_zero_right_rev");
            }
            if (op == "TLA.add" || op == "Nat.add") && self.is_zero(&a) && self.exprs_equal(&b, lhs)
            {
                return Some("add_zero_left_rev");
            }
        }

        None
    }

    /// Try to prove an equality goal using hypothesis definitions.
    pub(super) fn try_arith_simplify_with_hypotheses(
        &self,
        goal: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        let (goal_lhs, goal_rhs) = self.extract_equality(goal)?;

        let goal_rhs_norm = self.normalize_arith(&goal_rhs);

        if self.trace {
            eprintln!(
                "[TLA] try_arith_simplify_with_hypotheses: goal {} = {} (normalized RHS: {})",
                self.expr_debug(&goal_lhs),
                self.expr_debug(&goal_rhs),
                self.expr_debug(&goal_rhs_norm)
            );
        }

        for (i, hyp) in hypotheses.iter().enumerate() {
            if let Some((hyp_lhs, hyp_rhs)) = self.extract_equality(hyp) {
                if self.trace {
                    eprintln!(
                        "[TLA]   hyp[{}] before norm: {} = {}",
                        i,
                        self.expr_debug(&hyp_lhs),
                        self.expr_debug(&hyp_rhs)
                    );
                }

                let hyp_lhs_norm = self.normalize_arith(&hyp_lhs);
                let hyp_rhs_norm = self.normalize_arith(&hyp_rhs);

                if self.trace {
                    eprintln!(
                        "[TLA]   checking hyp[{}]: {} = {}",
                        i,
                        self.expr_debug(&hyp_lhs_norm),
                        self.expr_debug(&hyp_rhs_norm)
                    );
                }

                // Case 1: direct match
                if self.exprs_equal(&hyp_lhs_norm, &goal_lhs)
                    && self.exprs_equal(&hyp_rhs_norm, &goal_rhs_norm)
                {
                    if self.trace {
                        eprintln!("[TLA]   hyp[{}] matches goal (direct)", i);
                    }
                    return Some(format!(
                        "{{\"tactic\":\"arith_simplify_hyp\",\"hypothesis\":{},\"direction\":\"direct\",\"status\":\"proved\"}}",
                        i
                    ));
                }

                // Case 2: symmetric
                if self.exprs_equal(&hyp_lhs_norm, &goal_rhs_norm)
                    && self.exprs_equal(&hyp_rhs_norm, &goal_lhs)
                {
                    if self.trace {
                        eprintln!("[TLA]   hyp[{}] matches goal (symmetric)", i);
                    }
                    return Some(format!(
                        "{{\"tactic\":\"arith_simplify_hyp\",\"hypothesis\":{},\"direction\":\"symmetric\",\"status\":\"proved\"}}",
                        i
                    ));
                }

                // Case 3: goal LHS also needs normalization
                let goal_lhs_norm = self.normalize_arith(&goal_lhs);
                if self.exprs_equal(&hyp_lhs_norm, &goal_lhs_norm)
                    && self.exprs_equal(&hyp_rhs_norm, &goal_rhs_norm)
                {
                    if self.trace {
                        eprintln!("[TLA]   hyp[{}] matches goal (both normalized)", i);
                    }
                    return Some(format!(
                        "{{\"tactic\":\"arith_simplify_hyp\",\"hypothesis\":{},\"direction\":\"both_normalized\",\"status\":\"proved\"}}",
                        i
                    ));
                }

                // Case 4: Substitute hypothesis into goal and simplify
                let goal_lhs_subst =
                    self.substitute_ih(&goal_lhs_norm, &hyp_lhs_norm, &hyp_rhs_norm);
                let goal_lhs_subst_norm = self.normalize_arith(&goal_lhs_subst);

                if self.trace {
                    eprintln!(
                        "[TLA]   after substituting hyp[{}]: {} vs {}",
                        i,
                        self.expr_debug(&goal_lhs_subst_norm),
                        self.expr_debug(&goal_rhs_norm)
                    );
                }

                if self.exprs_equal(&goal_lhs_subst_norm, &goal_rhs_norm) {
                    if self.trace {
                        eprintln!("[TLA]   hyp[{}] proves goal via substitution", i);
                    }
                    return Some(format!(
                        "{{\"tactic\":\"arith_simplify_hyp\",\"hypothesis\":{},\"direction\":\"substitution\",\"status\":\"proved\"}}",
                        i
                    ));
                }
            }
        }

        None
    }

    /// Try to prove an induction step case for arithmetic identities.
    ///
    /// SOUNDNESS: this used to carry four bespoke shape-only rules
    /// (`add_zero_succ`, `zero_add_succ`, `mul_one_succ`, `mul_zero_succ`) that
    /// accepted the step `P(n) → P(succ n)` after matching only the *left*
    /// operand shapes of the premise and conclusion equalities — the right-hand
    /// sides and the other operand were never inspected. That let genuinely
    /// false goals through, e.g. `∀n: (n+0)=(2*n)` (add_zero_succ fires without
    /// checking the RHS `2*n`) and `∀n: (n*1)=(n+n)` (mul_one_succ ignores the
    /// RHS `n+n`). Those rules are removed. The only accepting path is now the
    /// `normalize_both` check below, which normalizes BOTH sides of BOTH
    /// equalities and accepts only when each equality's two sides are provably
    /// equal after normalization — a genuine, RHS-inspecting identity check. If
    /// it does not hold, return `None` so the caller falls through to a sound
    /// prover (fail-closed).
    pub(super) fn try_arith_step_case(&self, step_body: &Expr) -> Option<String> {
        if let ExprKind::Pi(_, premise, conclusion) = step_body.kind() {
            if let Some((lhs_p, rhs_p)) = self.extract_equality(premise) {
                if let Some((lhs_c, rhs_c)) = self.extract_equality(conclusion) {
                    // Accept only when each equality is itself a true identity
                    // after full (both-sides) normalization. This inspects the
                    // right-hand sides, so `n+0 = 2*n` and `n*1 = n+n` are
                    // correctly rejected (n ≠ 2*n, n ≠ n+n).
                    let lhs_p_norm = self.normalize_arith(&lhs_p);
                    let rhs_p_norm = self.normalize_arith(&rhs_p);
                    let lhs_c_norm = self.normalize_arith(&lhs_c);
                    let rhs_c_norm = self.normalize_arith(&rhs_c);

                    if self.exprs_equal(&lhs_p_norm, &rhs_p_norm)
                        && self.exprs_equal(&lhs_c_norm, &rhs_c_norm)
                    {
                        return Some("{\"tactic\":\"arith_step\",\"method\":\"normalize_both\",\"status\":\"proved\"}".to_string());
                    }
                }
            }
        }

        None
    }
}
