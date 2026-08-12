// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Expression extractors, predicates, and utility functions for TLA+ tactics.

use super::TlaTacticEngine;
use clean_kernel::{Expr, ExprKind};

impl TlaTacticEngine {
    /// Extract P and Q from implication P → Q.
    ///
    /// Implications can be encoded as:
    /// 1. Or(Not(P), Q) - classical encoding
    /// 2. Pi(_, P, Q) where Q doesn't depend on the binding - non-dependent implication
    pub(super) fn extract_implication(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        // Check for Or(Not(P), Q) encoding
        if let Some((left, right)) = self.extract_or(expr) {
            if let Some(p) = self.extract_not(&left) {
                return Some((p, right));
            }
        }

        // Check for Pi(_, P, Q) non-dependent implication
        if let ExprKind::Pi(_, p, q) = expr.kind() {
            if !q.has_loose_bvars() {
                return Some((p.as_ref().clone(), q.as_ref().clone()));
            }
        }

        // Check for TLA.implies encoding if it exists
        if let ExprKind::App(f, q) = expr.kind() {
            if let ExprKind::App(implies_op, p) = f.kind() {
                if let ExprKind::Const(name, _) = implies_op.kind() {
                    if name.to_string() == "TLA.implies" {
                        return Some((p.as_ref().clone(), q.as_ref().clone()));
                    }
                }
            }
        }

        None
    }

    /// Extract P from Not(P)
    pub(super) fn extract_not(&self, expr: &Expr) -> Option<Expr> {
        if let ExprKind::App(not, inner) = expr.kind() {
            if let ExprKind::Const(name, _) = not.kind() {
                let s = name.to_string();
                if s == "Not" || s == "TLA.not" || s == "not" {
                    return Some(inner.as_ref().clone());
                }
            }
        }
        None
    }

    /// Extract P and Q from Or(P, Q)
    pub(super) fn extract_or(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        // Pattern: Or(P, Q) encoded as App(App(Or, P), Q)
        if let ExprKind::App(f, q) = expr.kind() {
            if let ExprKind::App(or_op, p) = f.kind() {
                if let ExprKind::Const(name, _) = or_op.kind() {
                    let s = name.to_string();
                    if s == "Or" || s == "TLA.or" || s == "or" {
                        return Some((p.as_ref().clone(), q.as_ref().clone()));
                    }
                }
            }
        }
        None
    }

    /// Extract equality from goal (Eq or TLA.eq)
    pub(super) fn extract_equality(&self, goal: &Expr) -> Option<(Expr, Expr)> {
        // Pattern 1: App(App(Eq _, lhs), rhs)
        // Pattern 2: App(App(TLA.eq, lhs), rhs)
        if let ExprKind::App(f, rhs) = goal.kind() {
            if let ExprKind::App(eq_or_inner, lhs) = f.kind() {
                // Check if this is an equality
                if let ExprKind::App(eq_const, _ty) = eq_or_inner.kind() {
                    if let ExprKind::Const(name, _) = eq_const.kind() {
                        if name.to_string() == "Eq" {
                            return Some((lhs.as_ref().clone(), rhs.as_ref().clone()));
                        }
                    }
                }
                // Direct TLA.eq application
                if let ExprKind::Const(name, _) = eq_or_inner.kind() {
                    if name.to_string() == "TLA.eq" || name.to_string() == "Eq" {
                        return Some((lhs.as_ref().clone(), rhs.as_ref().clone()));
                    }
                }
            }
        }
        None
    }

    /// Extract binary arithmetic operation: returns (op_name, arg1, arg2)
    pub(super) fn extract_binary_arith(&self, expr: &Expr) -> Option<(String, Expr, Expr)> {
        if let ExprKind::App(f, b) = expr.kind() {
            if let ExprKind::App(op_expr, a) = f.kind() {
                if let ExprKind::Const(op_name, _) = op_expr.kind() {
                    return Some((op_name.to_string(), a.as_ref().clone(), b.as_ref().clone()));
                }
            }
        }
        None
    }

    /// Extract comparison from expression: returns (op, lhs, rhs)
    /// Pattern: App(App(TLA.op, lhs), rhs) where op is gt/lt/ge/le
    pub(super) fn extract_comparison(&self, expr: &Expr) -> Option<(String, Expr, Expr)> {
        if let ExprKind::App(f, rhs) = expr.kind() {
            if let ExprKind::App(op_expr, lhs) = f.kind() {
                if let ExprKind::Const(op_name, _) = op_expr.kind() {
                    let op = op_name.to_string();
                    if op == "TLA.gt"
                        || op == "TLA.lt"
                        || op == "TLA.ge"
                        || op == "TLA.le"
                        || op == "Nat.blt"
                        || op == "Nat.ble"
                    {
                        return Some((op, lhs.as_ref().clone(), rhs.as_ref().clone()));
                    }
                }
            }
        }
        None
    }

    /// Extract inner formula from TLA_always application
    /// Returns Some(P) if goal is FixedPoint.TLA_always P
    pub(super) fn extract_always(&self, expr: &Expr) -> Option<Expr> {
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "FixedPoint.TLA_always" {
                    return Some(arg.as_ref().clone());
                }
            }
        }
        None
    }

    /// Extract inner formula from TLA_eventually application
    /// Returns Some(P) if goal is FixedPoint.TLA_eventually P
    pub(super) fn extract_eventually(&self, expr: &Expr) -> Option<Expr> {
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "FixedPoint.TLA_eventually" {
                    return Some(arg.as_ref().clone());
                }
            }
        }
        None
    }

    /// Extract P and Q from TLA_leads_to application
    /// Returns Some((P, Q)) if goal is FixedPoint.TLA_leads_to P Q
    pub(super) fn extract_leads_to(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        // leads_to is binary: TLA_leads_to P Q
        if let ExprKind::App(f, q) = expr.kind() {
            if let ExprKind::App(g, p) = f.kind() {
                if let ExprKind::Const(name, _) = g.kind() {
                    if name.to_string() == "FixedPoint.TLA_leads_to" {
                        return Some((p.as_ref().clone(), q.as_ref().clone()));
                    }
                }
            }
        }
        None
    }

    /// Extract `(vars, action)` from a weak-fairness application.
    ///
    /// Returns `Some((vars, action))` if `expr` is
    /// `FixedPoint.TLA_weak_fairness vars action` (the encoding produced for a
    /// `WF_vars(A)` formula in [`crate::encoding`]).
    pub(super) fn extract_weak_fairness(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        self.extract_binary_const(expr, "FixedPoint.TLA_weak_fairness")
    }

    /// Extract `(vars, action)` from a strong-fairness application.
    ///
    /// Returns `Some((vars, action))` if `expr` is
    /// `FixedPoint.TLA_strong_fairness vars action` (the encoding produced for
    /// an `SF_vars(A)` formula in [`crate::encoding`]).
    pub(super) fn extract_strong_fairness(&self, expr: &Expr) -> Option<(Expr, Expr)> {
        self.extract_binary_const(expr, "FixedPoint.TLA_strong_fairness")
    }

    /// Extract the two arguments of a binary constant application
    /// `App(App(Const(name), a), b)` → `Some((a, b))`.
    fn extract_binary_const(&self, expr: &Expr, name: &str) -> Option<(Expr, Expr)> {
        if let ExprKind::App(f, b) = expr.kind() {
            if let ExprKind::App(g, a) = f.kind() {
                if let ExprKind::Const(const_name, _) = g.kind() {
                    if const_name.to_string() == name {
                        return Some((a.as_ref().clone(), b.as_ref().clone()));
                    }
                }
            }
        }
        None
    }

    /// Extract inner expression from Nat.succ(x) → Some(x)
    pub(super) fn extract_succ(&self, expr: &Expr) -> Option<Expr> {
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    return Some(arg.as_ref().clone());
                }
            }
        }
        None
    }

    /// Extract the argument from succ(x) or (x + 1)
    pub(super) fn extract_succ_arg(&self, expr: &Expr) -> Option<Expr> {
        // Nat.succ x -> x
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    return Some(arg.as_ref().clone());
                }
            }
        }

        // x + 1 -> x
        if let Some((op, a, b)) = self.extract_binary_arith(expr) {
            if (op == "TLA.add" || op == "Nat.add" || op == "Add.add")
                && (self.is_one(&b) || self.is_one(&self.normalize_arith(&b)))
            {
                return Some(a);
            }
        }

        None
    }

    /// Extract a natural number literal from an expression.
    pub(super) fn extract_nat_lit(&self, expr: &Expr) -> Option<u64> {
        // Direct literal
        if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = expr.kind() {
            return n.to_u64();
        }
        // Int.ofNat n
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Int.ofNat" || s == "TLA.int" {
                    if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = arg.kind() {
                        return n.to_u64();
                    }
                }
            }
        }
        None
    }

    /// Check if expression is trivially true (Bool.true or similar)
    pub(super) fn is_trivially_true(&self, expr: &Expr) -> bool {
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            return s == "Bool.true" || s == "True" || s == "trivial";
        }

        // Check for trivially true comparisons
        if let Some((op, lhs, rhs)) = self.extract_comparison(expr) {
            // 0 >= 0, 0 <= 0, n = n, etc. are always true
            if self.exprs_equal(&lhs, &rhs) {
                // a = a, a <= a, a >= a are all true (reflexivity — the only
                // structural comparison shortcut that is sound for arbitrary,
                // possibly-untyped TLA+ values).
                if op == "Eq" || op == "TLA.eq" || op == "TLA.le" || op == "TLA.ge" {
                    return true;
                }
            }
            // SOUNDNESS: `n >= 0` is NOT unconditionally true. It holds only
            // when `n` is a natural number, but in TLA+'s untyped value universe
            // a bare variable ranges over all values (including negative
            // integers and non-numbers), so `x >= 0` for an unconstrained `x`
            // is a non-theorem. The former `(op == ge) && is_zero(rhs) => true`
            // branch certified that false obligation (`x >= 0`) as PROVED. It is
            // removed. Genuine `n >= 0` over a Nat-bound variable is still
            // discharged by the positivity machinery where the Nat typing is
            // established, not by this context-free structural shortcut.
            //
            // The strict-inequality shortcuts below ARE sound for arbitrary
            // integers: adding a positive constant to any integer strictly
            // increases it, so `n < n + k` / `n + k > n` (k > 0) hold
            // regardless of the sign of `n`.
            if (op == "TLA.lt" || op == "TLA.le") && self.is_expr_plus_positive(&lhs, &rhs) {
                return true;
            }
            if (op == "TLA.gt" || op == "TLA.ge") && self.is_expr_plus_positive(&rhs, &lhs) {
                return true;
            }
        }

        false
    }

    /// Check if rhs is lhs + k where k is positive.
    /// Returns true if rhs = lhs + k and k > 0.
    pub(super) fn is_expr_plus_positive(&self, lhs: &Expr, rhs: &Expr) -> bool {
        // Check if rhs is of form lhs + k where k > 0
        // Pattern: TLA.add lhs k
        if let ExprKind::App(f, k) = rhs.kind() {
            if let ExprKind::App(add, inner_lhs) = f.kind() {
                if let ExprKind::Const(name, _) = add.kind() {
                    if name.to_string() == "TLA.add" || name.to_string() == "Nat.add" {
                        // Check if inner_lhs == lhs and k is positive
                        if self.exprs_equal(inner_lhs, lhs) && self.is_positive_constant(k) {
                            return true;
                        }
                        // Also check swapped: k + lhs (commutativity)
                        if self.exprs_equal(k.as_ref(), lhs) && self.is_positive_constant(inner_lhs)
                        {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Check if expression is trivially false (Bool.false or False)
    pub(super) fn is_trivially_false(&self, expr: &Expr) -> bool {
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            return s == "Bool.false" || s == "False";
        }
        false
    }

    /// Check if an implication P → Q is trivially true.
    ///
    /// An implication is trivially true if:
    /// - Q is trivially true (True → True, P → True)
    /// - P is trivially false (False → Q)
    /// - P and Q are structurally equal (P → P)
    pub(super) fn is_implication_trivially_true(
        &self,
        antecedent: &Expr,
        consequent: &Expr,
    ) -> bool {
        self.is_trivially_true(consequent)
            || self.is_trivially_false(antecedent)
            || self.exprs_equal(antecedent, consequent)
    }

    /// Check if expression is zero (Nat.zero, TLA.zero, Int 0, etc.)
    pub(super) fn is_zero(&self, expr: &Expr) -> bool {
        // Named constants for zero
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            return s == "Nat.zero" || s == "TLA.zero" || s == "Int.zero" || s == "0";
        }
        // Literal 0
        if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = expr.kind() {
            return n.to_u64() == Some(0);
        }
        // Pattern: Int.ofNat 0 or TLA.int 0
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Int.ofNat" || s == "TLA.int" {
                    // Check if argument is literal 0
                    if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = arg.kind() {
                        return n.to_u64() == Some(0);
                    }
                }
            }
        }
        false
    }

    /// Check if expression is one (Nat.succ Nat.zero, etc.)
    pub(super) fn is_one(&self, expr: &Expr) -> bool {
        // Pattern: Nat.succ Nat.zero
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                let s = name.to_string();
                if s == "Nat.succ" {
                    return self.is_zero(arg);
                }
                // Pattern: Int.ofNat 1 or TLA.int 1
                if s == "Int.ofNat" || s == "TLA.int" {
                    if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = arg.kind() {
                        return n.to_u64() == Some(1);
                    }
                }
            }
        }
        // Literal 1
        if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = expr.kind() {
            return n.to_u64() == Some(1);
        }
        // Named constant
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            return s == "TLA.one" || s == "Nat.one" || s == "1";
        }
        false
    }

    /// Check if type is Nat
    pub(super) fn is_nat_type(&self, ty: &Expr) -> bool {
        if let ExprKind::Const(name, _) = ty.kind() {
            let s = name.to_string();
            return s == "Nat" || s == "TLA.Nat";
        }
        false
    }

    /// Check if expression represents the Nat set (TLA.Nat)
    pub(super) fn is_nat_set(&self, expr: &Expr) -> bool {
        if let ExprKind::Const(name, _) = expr.kind() {
            let s = name.to_string();
            return s == "TLA.Nat" || s == "Nat";
        }
        false
    }

    /// Check if expr represents (BVar(0) + 1) or (Nat.succ BVar(0))
    pub(super) fn is_succ_of_bvar0(&self, expr: &Expr) -> bool {
        // Direct succ: Nat.succ BVar(0)
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Nat.succ" {
                    if let ExprKind::BVar(0) = arg.kind() {
                        return true;
                    }
                }
            }
        }

        // Addition form: BVar(0) + 1 or TLA.add BVar(0) (Int.ofNat 1)
        if let Some((op, a, b)) = self.extract_binary_arith(expr) {
            if op == "TLA.add" || op == "Nat.add" || op == "Add.add" {
                // Check a is BVar(0) and b is 1
                if let ExprKind::BVar(0) = a.kind() {
                    if self.is_one(&b) || self.is_one(&self.normalize_arith(&b)) {
                        return true;
                    }
                }
            }
        }

        false
    }

    /// Check if expression is Nat.succ(something)
    pub(super) fn is_succ_expr(&self, expr: &Expr) -> bool {
        if let ExprKind::App(f, _) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                return name.to_string() == "Nat.succ";
            }
        }
        false
    }

    /// Check whether an expression is *provably* nonzero.
    ///
    /// Used as the divisor≠0 side-condition for the `0 / b → 0` and
    /// `0 % b → 0` rewrites. This is deliberately conservative: it returns
    /// `true` only for values that are syntactically, unconditionally positive
    /// (a positive numeric literal, `1`, or a `Nat.succ _` / `_ + k>0` form).
    /// A bare variable, or any expression whose value could be `0`, returns
    /// `false` so the definedness-sensitive rewrite does NOT fire.
    pub(super) fn is_provably_nonzero(&self, expr: &Expr) -> bool {
        // `is_positive_constant`: positive literals, `1`, and `Nat.succ _`.
        // `is_add_positive`: `n + k` with a positive constant addend (≥ k > 0
        // for Nat). Anything else (bare variable, opaque term) could be 0.
        self.is_positive_constant(expr) || self.is_add_positive(expr)
    }

    /// Check if expression is a positive constant (1, 2, 3, etc.)
    pub(super) fn is_positive_constant(&self, expr: &Expr) -> bool {
        // Literal > 0
        if let ExprKind::Lit(clean_kernel::Literal::Nat(n)) = expr.kind() {
            return n.to_u64().is_some_and(|v| v > 0);
        }
        // Nat.succ anything is positive
        if self.is_succ_expr(expr) {
            return true;
        }
        // 1 in various forms
        if self.is_one(expr) {
            return true;
        }
        false
    }

    /// Check if expression is n + k where k is a positive constant.
    /// This is always > 0 for natural numbers since n >= 0.
    pub(super) fn is_add_positive(&self, expr: &Expr) -> bool {
        // Pattern: TLA.add n k where k > 0
        if let ExprKind::App(f, arg2) = expr.kind() {
            if let ExprKind::App(add, arg1) = f.kind() {
                if let ExprKind::Const(name, _) = add.kind() {
                    if name.to_string() == "TLA.add" || name.to_string() == "Nat.add" {
                        // Check if either argument is a positive constant
                        if self.is_positive_constant(arg1) || self.is_positive_constant(arg2) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    /// Check if two expressions are structurally equal
    pub(super) fn exprs_equal(&self, a: &Expr, b: &Expr) -> bool {
        // Simple structural equality check
        a == b
    }

    /// Debug string for an expression (for tracing)
    pub(super) fn expr_debug(&self, expr: &Expr) -> String {
        match expr.kind() {
            ExprKind::Const(name, _) => name.to_string(),
            ExprKind::BVar(i) => format!("#{}", i),
            ExprKind::FVar(id) => format!("?{}", id.as_u64()),
            ExprKind::App(f, a) => format!("({} {})", self.expr_debug(f), self.expr_debug(a)),
            ExprKind::Lam(_, ty, body) => {
                format!("(λ:{} {})", self.expr_debug(ty), self.expr_debug(body))
            }
            ExprKind::Pi(_, ty, body) => {
                format!("(Π:{} {})", self.expr_debug(ty), self.expr_debug(body))
            }
            ExprKind::Lit(lit) => format!("{:?}", lit),
            _ => "...".to_string(),
        }
    }

    /// Search for a matching subexpression.
    pub(super) fn find_subexpr<T, F>(&self, expr: &Expr, f: &mut F) -> Option<T>
    where
        F: FnMut(&Expr) -> Option<T>,
    {
        if let Some(found) = f(expr) {
            return Some(found);
        }

        match expr.kind() {
            ExprKind::App(fun, arg) => self
                .find_subexpr(fun, f)
                .or_else(|| self.find_subexpr(arg, f)),
            ExprKind::Lam(_, ty, body) => self
                .find_subexpr(ty, f)
                .or_else(|| self.find_subexpr(body, f)),
            ExprKind::Pi(_, ty, body) => self
                .find_subexpr(ty, f)
                .or_else(|| self.find_subexpr(body, f)),
            _ => None,
        }
    }
}
