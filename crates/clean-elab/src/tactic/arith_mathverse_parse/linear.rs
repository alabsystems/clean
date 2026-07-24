// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Linear expression parsing and mathverse constraint negation.

use clean_kernel::{Expr, ExprKind};

use crate::stack_safe;
use crate::tactic::arith_field_simp::get_app_fn;
use crate::tactic::arithmetic::{big_nat_to_i64, LinearExpr};
use crate::tactic::omega_tactic::OmegaConstraint;

/// Convert expression to linear expression.
///
/// When `whnf_fn` is `Some`, unrecognized App sub-expressions are
/// WHNF-normalized and retried. This sees through definitions wrapping
/// arithmetic operators (e.g., `myAdd` → `HAdd.hAdd`).
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// REQUIRES: When present, `whnf_fn` preserves expression semantics
/// ENSURES: Nat/Int literals, `Nat.zero`, `Int.zero`, `Nat.one`, `Int.one` → constant
/// ENSURES: `FVar` → single-variable linear expression
/// ENSURES: `Int.ofNat e` preserves the linear structure of `e`
/// ENSURES: `add`/`sub` → sum/difference of recursive results
/// ENSURES: `mul` → scaled result only when one operand is constant (linearity)
/// ENSURES: `neg`/`Neg` → negated expression; `Nat.succ` → `inner + 1`
/// ENSURES: Returns `None` for non-linear or unrecognized expressions
/// ENSURES: Recursion is stack-safe
pub(crate) fn expr_to_linear(
    expr: &Expr,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<LinearExpr> {
    stack_safe(|| {
        let result = expr_to_linear_direct(expr, whnf_fn);
        if result.is_some() {
            return result;
        }
        // WHNF fallback for unrecognized App sub-expressions (#685).
        // Only try if we have a WHNF function and the expression is an
        // application (definitions wrapping arithmetic operators).
        if let Some(whnf) = whnf_fn {
            if matches!(expr.kind(), ExprKind::App(_, _)) {
                let normalized = whnf(expr);
                if normalized != *expr {
                    return expr_to_linear_direct(&normalized, whnf_fn);
                }
            }
        }
        None
    })
}

/// Direct parse of a linear expression without WHNF fallback.
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Same recognition rules as `expr_to_linear` but without WHNF retry
/// ENSURES: Returns `None` immediately for unrecognized top-level expressions
fn expr_to_linear_direct(
    expr: &Expr,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<LinearExpr> {
    match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => {
            big_nat_to_i64(n).map(LinearExpr::constant)
        }
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            if name_str == "Nat.zero" || name_str == "Int.zero" {
                Some(LinearExpr::constant(0))
            } else if name_str == "Nat.one" || name_str == "Int.one" {
                Some(LinearExpr::constant(1))
            } else {
                None
            }
        }
        ExprKind::FVar(id) => Some(LinearExpr::var(id.as_u64() as usize)),
        ExprKind::App(f, arg) => {
            // Check for binary operations
            if let ExprKind::App(f2, arg1) = f.kind() {
                if let ExprKind::Const(name, _) = get_app_fn(f2).kind() {
                    let name_str = name.to_string();

                    if name_str.contains("add") || name_str.contains("Add") {
                        let left = expr_to_linear(arg1, whnf_fn)?;
                        let right = expr_to_linear(arg, whnf_fn)?;
                        return Some(left.add(&right));
                    }
                    if name_str.contains("sub") || name_str.contains("Sub") {
                        let left = expr_to_linear(arg1, whnf_fn)?;
                        let right = expr_to_linear(arg, whnf_fn)?;
                        return Some(left.sub(&right));
                    }
                    if name_str.contains("mul") || name_str.contains("Mul") {
                        // One side must be constant for linearity
                        if let Some(left) = expr_to_linear(arg1, whnf_fn) {
                            if left.is_constant() {
                                if let Some(right) = expr_to_linear(arg, whnf_fn) {
                                    return Some(right.scale(left.constant));
                                }
                            }
                        }
                        if let Some(right) = expr_to_linear(arg, whnf_fn) {
                            if right.is_constant() {
                                if let Some(left) = expr_to_linear(arg1, whnf_fn) {
                                    return Some(left.scale(right.constant));
                                }
                            }
                        }
                    }
                }
            }
            // Check for unary operations
            if let ExprKind::Const(name, _) = f.kind() {
                let name_str = name.to_string();
                if name_str.contains("neg") || name_str.contains("Neg") {
                    let inner = expr_to_linear(arg, whnf_fn)?;
                    return Some(inner.scale(-1));
                }
                if name_str == "Int.ofNat" {
                    return expr_to_linear(arg, whnf_fn);
                }
                if name_str == "Nat.succ" {
                    let inner = expr_to_linear(arg, whnf_fn)?;
                    return Some(inner.add(&LinearExpr::constant(1)));
                }
            }
            None
        }
        _ => None,
    }
}

/// Extract a constant value from an expression
///
/// REQUIRES: `expr` is a well-formed Lean expression
/// ENSURES: Returns `Some(n)` for Nat literals, `Nat.zero`/`Int.zero` (→ 0),
///   `Nat.one`/`Int.one` (→ 1), and `OfNat.ofNat` wrappers
/// ENSURES: Returns `None` for non-constant expressions
/// ENSURES: Recursion is stack-safe
pub(crate) fn extract_constant(expr: &Expr) -> Option<i64> {
    stack_safe(|| match expr.kind() {
        ExprKind::Lit(clean_kernel::expr::Literal::Nat(n)) => big_nat_to_i64(n),
        ExprKind::Const(name, _) => {
            let name_str = name.to_string();
            if name_str == "Nat.zero" || name_str == "Int.zero" {
                Some(0)
            } else if name_str == "Nat.one" || name_str == "Int.one" {
                Some(1)
            } else {
                None
            }
        }
        // Handle OfNat.ofNat applications
        ExprKind::App(f, arg) => {
            if let ExprKind::App(f2, val) = f.kind() {
                if let ExprKind::Const(name, _) = get_app_fn(f2).kind() {
                    let name_str = name.to_string();
                    if name_str.contains("OfNat.ofNat") {
                        // The numeric value is embedded in `val`
                        return extract_constant(val);
                    }
                }
            }
            extract_constant(arg)
        }
        _ => None,
    })
}

/// Negate an mathverse constraint
///
/// REQUIRES: `constraint` is a valid `OmegaConstraint`
/// ENSURES: `Le(e)` → `Le(-e + 1)` (¬(e ≤ 0) ⟺ e > 0 ⟺ e ≥ 1 ⟺ -e + 1 ≤ 0)
/// ENSURES: `Lt(e)` → `Le(-e)` (¬(e < 0) ⟺ -e ≤ 0)
/// ENSURES: `Eq(e)` → `Ne(e)` and `Ne(e)` → `Eq(e)`
/// ENSURES: `Mod{r=0}` → `NotMod`, `Mod{m=2}` → `Mod` with flipped remainder,
///   `Mod{r≠0,m≠2}` → `NotLinearMod`
/// ENSURES: `NotMod` → `Mod{r=0}`, `LinearMod` ↔ `NotLinearMod`
/// ENSURES: Always returns `Some` (all variants have defined negations)
pub(crate) fn negate_mathverse_constraint(constraint: &OmegaConstraint) -> Option<OmegaConstraint> {
    match constraint {
        OmegaConstraint::Le(e) => {
            // ¬(e ≤ 0)  ⟺  e > 0  ⟺  e ≥ 1  ⟺  -e + 1 ≤ 0  (integer tightening).
            let mut shifted = e.scale(-1);
            shifted.constant += 1;
            Some(OmegaConstraint::Le(shifted))
        }
        OmegaConstraint::Lt(e) => Some(OmegaConstraint::Le(e.scale(-1))),
        OmegaConstraint::Eq(e) => Some(OmegaConstraint::Ne(e.clone())),
        OmegaConstraint::Ne(e) => Some(OmegaConstraint::Eq(e.clone())),
        OmegaConstraint::Mod {
            var,
            remainder,
            modulus,
        } => {
            if *modulus == 2 {
                // Parity: ¬(Even) ⟺ Odd, ¬(Odd) ⟺ Even
                Some(OmegaConstraint::Mod {
                    var: *var,
                    remainder: 1 - *remainder,
                    modulus: 2,
                })
            } else if *remainder == 0 {
                // ¬(m ∣ x) ⟺ x % m ≠ 0
                Some(OmegaConstraint::NotMod {
                    var: *var,
                    modulus: *modulus,
                })
            } else {
                // ¬(x ≡ r (mod m)): use NotLinearMod to preserve remainder
                Some(OmegaConstraint::NotLinearMod {
                    expr: LinearExpr::var(*var),
                    remainder: *remainder,
                    modulus: *modulus,
                })
            }
        }
        OmegaConstraint::NotMod { var, modulus } => {
            // ¬(¬(m ∣ x)) ⟺ x ≡ 0 (mod m)
            Some(OmegaConstraint::Mod {
                var: *var,
                remainder: 0,
                modulus: *modulus,
            })
        }
        OmegaConstraint::LinearMod {
            expr,
            remainder,
            modulus,
        } => {
            // ¬(expr ≡ r (mod m))  ⟺  expr ≢ r (mod m)
            Some(OmegaConstraint::NotLinearMod {
                expr: expr.clone(),
                remainder: *remainder,
                modulus: *modulus,
            })
        }
        OmegaConstraint::NotLinearMod {
            expr,
            remainder,
            modulus,
        } => {
            // ¬(expr ≢ r (mod m))  ⟺  expr ≡ r (mod m)
            Some(OmegaConstraint::LinearMod {
                expr: expr.clone(),
                remainder: *remainder,
                modulus: *modulus,
            })
        }
    }
}
