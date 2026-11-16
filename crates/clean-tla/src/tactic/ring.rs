// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ring tactic — polynomial normalization for algebraic equality.

use super::TlaTacticEngine;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Try ring tactic on a step case with IH substitution.
    ///
    /// For induction step cases like:
    ///   IH: 2*tri(n) = n*(n+1)
    ///   Goal: 2*tri(succ n) = (succ n)*((succ n)+1)
    ///   Recursive def: tri(succ n) = tri(n) + (n+1)
    ///
    /// This expands tri(succ n) using the recursive def, substitutes IH,
    /// then uses ring to verify the algebraic equality.
    pub(super) fn try_ring_step_case(
        &self,
        step_body: &Expr,
        hypotheses: &[Expr],
    ) -> Option<String> {
        // Extract P(n) → P(succ n)
        let ExprKind::Pi(_, p_n, p_succ_n) = step_body.kind() else {
            return None;
        };

        // Extract equalities from IH and goal
        let (ih_lhs, ih_rhs) = self.extract_equality(p_n)?;
        let (goal_lhs, goal_rhs) = self.extract_equality(p_succ_n)?;

        if self.trace {
            eprintln!(
                "[TLA] ring_step: IH: {} = {}",
                self.expr_debug(&ih_lhs),
                self.expr_debug(&ih_rhs)
            );
            eprintln!(
                "[TLA] ring_step: goal: {} = {}",
                self.expr_debug(&goal_lhs),
                self.expr_debug(&goal_rhs)
            );
        }

        // Find a recursive definition in hypotheses
        for hyp in hypotheses.iter() {
            if let Some(rewrite) = self.extract_recursive_definition(hyp) {
                // Apply recursive definition to goal_lhs
                if let Some(rewritten_lhs) = self.apply_recursive_rewrite(&goal_lhs, &rewrite) {
                    if self.trace {
                        eprintln!(
                            "[TLA] ring_step: after recursive rewrite: {}",
                            self.expr_debug(&rewritten_lhs)
                        );
                    }

                    // Expand and substitute IH
                    let expanded = self.normalize_arith(&rewritten_lhs);
                    let ih_lhs_norm = self.normalize_arith(&ih_lhs);
                    let ih_rhs_norm = self.normalize_arith(&ih_rhs);
                    let substituted = self.substitute_ih(&expanded, &ih_lhs_norm, &ih_rhs_norm);

                    if self.trace {
                        eprintln!(
                            "[TLA] ring_step: after IH substitution: {}",
                            self.expr_debug(&substituted)
                        );
                    }

                    // Convert to polynomials and compare. SOUNDNESS: a `None`
                    // side is UNDECIDED (overflow or subtraction) — it must not
                    // be treated as equal to anything, so only accept when both
                    // sides are `Some` and structurally identical.
                    let lhs_poly = self.expr_to_polynomial(&substituted);
                    let rhs_poly = self.expr_to_polynomial(&goal_rhs);

                    if self.trace {
                        eprintln!("[TLA] ring_step: LHS poly = {:?}", lhs_poly);
                        eprintln!("[TLA] ring_step: RHS poly = {:?}", rhs_poly);
                    }

                    if let (Some(l), Some(r)) = (&lhs_poly, &rhs_poly) {
                        if l == r {
                            return Some("{\"tactic\":\"ring\",\"method\":\"step_case_ih\",\"status\":\"proved\"}".to_string());
                        }
                    }
                }
            }
        }

        None
    }

    /// Convert an expression to canonical polynomial form.
    ///
    /// A polynomial is represented as a sorted list of monomials. Each monomial
    /// is `(coefficient, sorted variable names)`.
    ///
    /// SOUNDNESS: returns `None` when the expression cannot be soundly
    /// canonicalized as an exact integer polynomial. This happens when:
    /// * a coefficient product or sum overflows `i64` (so distinct values could
    ///   otherwise alias — e.g. `3037000500²` and `4000000000²` both saturating
    ///   to `i64::MAX`), or
    /// * the expression contains a subtraction node (`TLA.sub`/`Nat.sub`/
    ///   `Sub.sub`). Subtraction was modeled as ring (group) negation, which
    ///   asserts identities like `(2-5)+5 = 2` that are false under TLA+/Nat
    ///   truncated subtraction; refusing to canonicalize any subtraction is
    ///   conservative and never certifies a subtraction identity.
    ///
    /// Callers must treat `None` as UNDECIDED (not "equal"): a `proved` verdict
    /// requires an exact, non-saturated polynomial identity on both sides.
    pub(super) fn expr_to_polynomial(&self, expr: &Expr) -> Option<Vec<(i64, Vec<String>)>> {
        let mut poly = self.expr_to_poly_internal(expr)?;
        // Combine like terms and sort
        poly = self.combine_like_terms(poly)?;
        poly.sort_by(|a, b| {
            // Sort by degree (length of vars) then lexicographically
            match a.1.len().cmp(&b.1.len()) {
                std::cmp::Ordering::Equal => a.1.cmp(&b.1),
                ord => ord,
            }
        });
        // Remove zero terms
        poly.retain(|(coef, _)| *coef != 0);
        Some(poly)
    }

    /// Internal recursive conversion to polynomial.
    ///
    /// Returns `None` on any overflow or unsupported (subtraction) node so the
    /// whole comparison is treated as undecided rather than asserting a false
    /// equality. See [`Self::expr_to_polynomial`].
    fn expr_to_poly_internal(&self, expr: &Expr) -> Option<Vec<(i64, Vec<String>)>> {
        // Handle numeric literals and constants
        if let Some(n) = self.extract_nat_lit(expr) {
            // A Nat literal that does not fit in i64 cannot be an exact
            // coefficient; refuse rather than truncate.
            let c = i64::try_from(n).ok()?;
            return Some(vec![(c, vec![])]);
        }

        // Handle zero/one constants
        if self.is_zero(expr) {
            return Some(vec![(0, vec![])]);
        }
        if self.is_one(expr) {
            return Some(vec![(1, vec![])]);
        }

        // Handle variables and constants
        if let ExprKind::BVar(idx) = expr.kind() {
            return Some(vec![(1, vec![format!("#BVar{}", idx)])]);
        }
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            // Skip Nat type itself
            if s == "Nat" || s == "TLA.Nat" {
                return Some(vec![(0, vec![])]);
            }
            // Skip Nat.zero/one already handled
            if s == "Nat.zero" || s == "TLA.zero" {
                return Some(vec![(0, vec![])]);
            }
            return Some(vec![(1, vec![s])]);
        }

        // Handle binary operations
        if let Some((op, a, b)) = self.extract_binary_arith(expr) {
            match op.as_str() {
                "TLA.add" | "Nat.add" | "Add.add" => {
                    // Addition: concatenate polynomials
                    let mut result = self.expr_to_poly_internal(&a)?;
                    result.extend(self.expr_to_poly_internal(&b)?);
                    return Some(result);
                }
                "TLA.mul" | "Nat.mul" | "Mul.mul" => {
                    let a_poly = self.expr_to_poly_internal(&a)?;
                    let b_poly = self.expr_to_poly_internal(&b)?;
                    // Multiplication: multiply each term in a by each term in b.
                    let mut result = Vec::new();
                    for (coef_a, vars_a) in &a_poly {
                        for (coef_b, vars_b) in &b_poly {
                            let mut vars = vars_a.clone();
                            vars.extend(vars_b.clone());
                            vars.sort();
                            // SOUNDNESS: coefficients come from attacker-
                            // controlled Nat literals, so their product can
                            // exceed i64::MAX. A plain `*` would overflow-panic
                            // under release overflow-checks; `saturating_mul`
                            // would clamp DISTINCT products to the same
                            // i64::MAX and thereby certify a FALSE equality
                            // (e.g. 3037000500² = 4000000000²). Use checked_mul
                            // and bail (None = undecided) on overflow so no
                            // spurious equality is asserted and the verifier
                            // neither crashes nor lies.
                            let coef = coef_a.checked_mul(*coef_b)?;
                            result.push((coef, vars));
                        }
                    }
                    return Some(result);
                }
                "TLA.sub" | "Nat.sub" | "Sub.sub" => {
                    // SOUNDNESS: do NOT model subtraction as ring negation.
                    // Over TLA+/Nat truncated subtraction (and to avoid the
                    // signed-cancellation that certified `(2-5)+5 = 2`), a
                    // subtraction node makes the polynomial form undecided.
                    // Refusing here means cancellation across a subtraction can
                    // never happen, so the ring tactic simply declines and the
                    // obligation falls through to a sound prover.
                    return None;
                }
                _ => {}
            }
        }

        // Handle Nat.succ: succ(x) = x + 1
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    let mut result = self.expr_to_poly_internal(arg)?;
                    result.push((1, vec![])); // Add 1
                    return Some(result);
                }
            }
        }

        // Handle function applications as opaque terms
        if let ExprKind::App(f, arg) = expr.kind() {
            // Create a symbolic name for this application
            let f_name = self.expr_debug(f);
            let arg_name = self.expr_debug(arg);
            let sym = format!("{}({})", f_name, arg_name);
            return Some(vec![(1, vec![sym])]);
        }

        // Fallback: treat as opaque variable
        let sym = self.expr_debug(expr);
        Some(vec![(1, vec![sym])])
    }

    /// Combine like terms in a polynomial.
    ///
    /// SOUNDNESS: returns `None` if summing like-term coefficients overflows
    /// `i64`. Saturating here would alias distinct polynomials; `checked_add`
    /// with a `None` bail keeps the comparison exact-or-undecided.
    fn combine_like_terms(&self, poly: Vec<(i64, Vec<String>)>) -> Option<Vec<(i64, Vec<String>)>> {
        use std::collections::HashMap;

        let mut term_map: HashMap<Vec<String>, i64> = HashMap::new();
        for (coef, vars) in poly {
            let entry = term_map.entry(vars).or_insert(0);
            *entry = entry.checked_add(coef)?;
        }

        Some(
            term_map
                .into_iter()
                .map(|(vars, coef)| (coef, vars))
                .collect(),
        )
    }
}

#[cfg(test)]
mod overflow_tests {
    use super::TlaTacticEngine;
    use clean_kernel::name::Name;
    use clean_kernel::Expr;

    /// Build `Int.ofNat n` exactly as the TLA encoding does for a positive
    /// integer literal (see `encoding.rs` `TlaExpr::Int`).
    fn int_of_nat(n: u64) -> Expr {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n),
        )
    }

    /// Build `TLA.mul a b` (curried application) as the encoding does.
    fn tla_mul(a: Expr, b: Expr) -> Expr {
        Expr::app(
            Expr::app(Expr::const_(Name::from_string("TLA.mul"), vec![]), a),
            b,
        )
    }

    /// Regression: `expr_to_polynomial` must neither overflow-panic NOR alias
    /// distinct overflowing products when coefficients come from large
    /// attacker-controlled Nat literals.
    ///
    /// 3037000500 * 3037000500 = 9_223_372_037_000_250_000 > i64::MAX
    /// (9_223_372_036_854_775_807). The old code used `saturating_mul`, which
    /// clamped BOTH `3037000500²` and `4000000000²` to i64::MAX — aliasing two
    /// distinct products and certifying the FALSE equality
    /// `3037000500² = 4000000000²`. The fix uses `checked_mul` and returns
    /// `None` (undecided) on overflow: no panic, and distinct overflowing
    /// products never collide because neither is representable.
    #[test]
    fn test_expr_to_polynomial_mul_overflow_is_undecided() {
        let engine = TlaTacticEngine::new();
        let big = 3_037_000_500u64;
        // Sanity: the product genuinely exceeds i64::MAX.
        assert!(
            (big as u128) * (big as u128) > i64::MAX as u128,
            "test literal must overflow i64 to exercise the guard"
        );

        // Must not panic; overflow yields None (undecided), not a saturated
        // (aliasing) coefficient.
        let expr = tla_mul(int_of_nat(big), int_of_nat(big));
        assert!(
            engine.expr_to_polynomial(&expr).is_none(),
            "overflowing product must be undecided (None), never a saturated i64::MAX"
        );

        // Two DISTINCT overflowing products must not be reported equal.
        let other = 4_000_000_000u64;
        let expr_other = tla_mul(int_of_nat(other), int_of_nat(other));
        let poly_a = engine.expr_to_polynomial(&expr);
        let poly_b = engine.expr_to_polynomial(&expr_other);
        assert!(
            !(poly_a.is_some() && poly_a == poly_b),
            "distinct overflowing products must never canonicalize to the same polynomial"
        );
    }
}
