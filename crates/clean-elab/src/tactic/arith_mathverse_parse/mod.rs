// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Mathverse tactic expression parsing
//!
//! Parses Lean 4 expressions into mathverse constraints and linear expressions.
//! Handles Even/Odd predicates, divisibility, modular arithmetic, and
//! comparison operators.

mod linear;

pub(crate) use linear::{expr_to_linear, extract_constant, negate_mathverse_constraint};

use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind};

use super::arithmetic::LinearExpr;
use super::omega_tactic::OmegaConstraint;
use crate::stack_safe;

/// Convert expression to mathverse constraint.
///
/// When `whnf_fn` is `Some`, sub-expressions that fail direct parsing are
/// WHNF-normalized and retried. This handles definitions wrapping arithmetic
/// or comparison operators (e.g., `myLe x y` unfolding to `LE.le ... x y`).
/// REQUIRES: `expr` is a well-formed arithmetic or proposition expression.
/// REQUIRES: When present, `whnf_fn` preserves the semantics of the
/// subexpressions it normalizes.
/// ENSURES: Recognized parity, divisibility, modular-equality, and
/// order/equality predicates are translated to corresponding `OmegaConstraint`
/// values.
/// ENSURES: Negated modular/parity constraints are converted to the matching
/// negated mathverse variants.
/// ENSURES: Returns `None` when the expression is outside the supported mathverse
/// fragment.
pub(crate) fn expr_to_mathverse_constraint(
    expr: &Expr,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<OmegaConstraint> {
    stack_safe(|| {
        // Check for Even/Odd predicates: `Even n` or `Odd n`
        // Even n ≡ ∃ k, n = 2 * k  ⟺  n ≡ 0 (mod 2)
        // Odd n ≡ ∃ k, n = 2 * k + 1  ⟺  n ≡ 1 (mod 2)
        if let ExprKind::App(f, arg) = expr.kind() {
            if let ExprKind::Const(name, _) = f.kind() {
                let name_str = name.to_string();
                if name_str == "Even" || name_str == "Nat.Even" || name_str == "Int.Even" {
                    // Even n ⟺ n ≡ 0 (mod 2)
                    if let Some(var) = extract_single_var(arg) {
                        return Some(OmegaConstraint::Mod {
                            var,
                            remainder: 0,
                            modulus: 2,
                        });
                    }
                }
                if name_str == "Odd" || name_str == "Nat.Odd" || name_str == "Int.Odd" {
                    // Odd n ⟺ n ≡ 1 (mod 2)
                    if let Some(var) = extract_single_var(arg) {
                        return Some(OmegaConstraint::Mod {
                            var,
                            remainder: 1,
                            modulus: 2,
                        });
                    }
                }
            }
            // Check for Even/Odd with type argument: `@Even Nat _ n` or `@Odd Int _ n`
            if let ExprKind::App(f2, arg2) = f.kind() {
                if let ExprKind::App(f3, _inst) = f2.kind() {
                    if let ExprKind::App(f4, _ty) = f3.kind() {
                        if let ExprKind::Const(name, _) = f4.kind() {
                            let name_str = name.to_string();
                            if name_str == "Even" {
                                // The actual argument is `arg`, the final one applied
                                if let Some(var) = extract_single_var(arg) {
                                    return Some(OmegaConstraint::Mod {
                                        var,
                                        remainder: 0,
                                        modulus: 2,
                                    });
                                }
                                // Sometimes the argument is wrapped differently
                                if let Some(var) = extract_single_var(arg2) {
                                    return Some(OmegaConstraint::Mod {
                                        var,
                                        remainder: 0,
                                        modulus: 2,
                                    });
                                }
                            }
                            if name_str == "Odd" {
                                if let Some(var) = extract_single_var(arg) {
                                    return Some(OmegaConstraint::Mod {
                                        var,
                                        remainder: 1,
                                        modulus: 2,
                                    });
                                }
                                if let Some(var) = extract_single_var(arg2) {
                                    return Some(OmegaConstraint::Mod {
                                        var,
                                        remainder: 1,
                                        modulus: 2,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }

        // Check for negated parity/divisibility:
        // - `Not (Even n)` → `Odd n`
        // - `Not (Odd n)` → `Even n`
        // - `Not (Dvd.dvd a b)` → `NotMod { var: b, modulus: a }`
        //
        // Not P in Lean is `P → False`, elaborated as `App (Const "Not") P`, and
        // after WHNF/delta it can appear structurally as the non-dependent arrow
        // `Pi (_ : P) => False`. Both forms are recognized here.
        if let Some(inner) = match_negation_inner(expr) {
            if let Some(constraint) = parse_negated_inner(&inner, whnf_fn) {
                return Some(constraint);
            }
        }

        // Check for Dvd (divisibility): `a ∣ b` or `Dvd.dvd a b`
        // a ∣ b ≡ ∃ k, b = a * k  ⟺  b ≡ 0 (mod a)
        if let ExprKind::App(f, b) = expr.kind() {
            if let ExprKind::App(f2, a) = f.kind() {
                // Check for `Dvd.dvd a b` pattern (with instance/type args)
                if let Some((divisor, dividend)) = match_dvd_app(f2, a, b) {
                    // a ∣ b  ⟺  b ≡ 0 (mod a)
                    if let Some(var) = extract_single_var(&dividend) {
                        if let Some(mod_val) = extract_constant(&divisor) {
                            if mod_val > 0 {
                                return Some(OmegaConstraint::Mod {
                                    var,
                                    remainder: 0,
                                    modulus: mod_val,
                                });
                            }
                        }
                    }
                }
            }
        }

        // Check for modular equality: `n % m = r` where m and r are constants
        // Pattern: Eq (HMod.hMod n m) r  ⟺  n ≡ r (mod m)
        if let Some(mod_constraint) = parse_mod_equality(expr, whnf_fn) {
            return Some(mod_constraint);
        }

        if let Some(comparison) = parse_direct_binary_comparison(expr, whnf_fn) {
            return Some(comparison);
        }

        // Check for comparison operators
        if let ExprKind::App(f, rhs) = expr.kind() {
            if let ExprKind::App(f2, lhs) = f.kind() {
                if let ExprKind::App(f3, _ty) = f2.kind() {
                    if let ExprKind::Const(name, _) = f3.kind() {
                        let name_str = name.to_string();

                        // Try to parse lhs and rhs as linear expressions
                        let lhs_lin = expr_to_linear(lhs, whnf_fn)?;
                        let rhs_lin = expr_to_linear(rhs, whnf_fn)?;
                        let diff = lhs_lin.sub(&rhs_lin);

                        if name_str.contains("LE.le") || name_str.contains("le") {
                            // lhs ≤ rhs  ⟺  lhs - rhs ≤ 0
                            return Some(OmegaConstraint::Le(diff));
                        }
                        if name_str.contains("LT.lt") || name_str.contains("lt") {
                            // lhs < rhs  ⟺  lhs - rhs < 0
                            return Some(OmegaConstraint::Lt(diff));
                        }
                        if name_str.contains("GE.ge") || name_str.contains("ge") {
                            // lhs ≥ rhs  ⟺  rhs - lhs ≤ 0
                            return Some(OmegaConstraint::Le(rhs_lin.sub(&lhs_lin)));
                        }
                        if name_str.contains("GT.gt") || name_str.contains("gt") {
                            // lhs > rhs  ⟺  rhs - lhs < 0
                            return Some(OmegaConstraint::Lt(rhs_lin.sub(&lhs_lin)));
                        }
                        if name_str.contains("Eq") {
                            // lhs = rhs  ⟺  lhs - rhs = 0
                            return Some(OmegaConstraint::Eq(diff));
                        }
                        if name_str.contains("Ne") {
                            // lhs ≠ rhs  ⟺  lhs - rhs ≠ 0
                            return Some(OmegaConstraint::Ne(diff));
                        }
                    }
                }
            }
        }
        None
    })
}

/// Recognize a negated proposition and return its inner proposition `P`.
///
/// Handles both surface forms of `¬P`:
/// - `App (Const "Not" _) P` — the elaborated `Not P` head.
/// - `Pi (_ : P) => False` — the definitional unfolding `P → False`, which
///   appears after callers WHNF-normalize a `Not` hypothesis/goal type. The
///   binder must not occur in the body (a genuine non-dependent arrow) and the
///   body must be `False`.
///
/// REQUIRES: `expr` is a well-formed proposition expression.
/// ENSURES: Returns `Some(P)` only for the two negation shapes above.
/// ENSURES: Returns `None` for any other expression, including dependent `Pi`s
/// and arrows whose codomain is not `False`.
fn match_negation_inner(expr: &Expr) -> Option<Expr> {
    match expr.kind() {
        ExprKind::App(f, inner) => {
            if let ExprKind::Const(name, _) = f.kind() {
                if name.to_string() == "Not" {
                    return Some(inner.as_ref().clone());
                }
            }
            None
        }
        // `P → False` is `Pi (_ : P) => False` with a body that ignores the
        // binder. This is the WHNF/delta unfolding of `Not P`.
        ExprKind::Pi(_bi, domain, body) => {
            let is_false = matches!(body.kind(), ExprKind::Const(n, _) if n.to_string() == "False");
            if is_false && !body.has_loose_bvar(0) {
                Some(domain.as_ref().clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Parse the inner proposition `P` of a negation `¬P` and return the constraint
/// for `¬P` (the negation of `P`'s constraint).
///
/// The inner `P` is parsed with the WHNF fallback (mirroring the top-level
/// callers): a raw comparison like `LE.le Nat inst a c` carries an instance
/// argument the direct comparison matcher does not peel, so it only becomes
/// recognizable after WHNF unfolds it to `Nat.le a c`. Parity/divisibility and
/// modular sub-cases keep their bespoke negations; every remaining constraint
/// (the linear `Le`/`Lt`/`Eq`/`Ne` relations) is negated via the shared
/// [`negate_mathverse_constraint`] helper — the exact same negation used to
/// negate the goal — so `¬(a ≤ 2)` → `a > 2`, `¬(a < b)` → `b ≤ a`,
/// `¬(a = 5)` → `a ≠ 5`, etc.
///
/// Soundness: the resulting constraint only guides the fail-closed solver
/// search; the final proof term is independently kernel-rechecked, so a wrong
/// constraint can never close a false goal.
///
/// REQUIRES: `inner` is the inner proposition of a `¬(...)` expression.
/// ENSURES: Returns `Some` only when `inner` parses to a known constraint whose
/// negation is defined; otherwise `None`.
fn parse_negated_inner(
    inner: &Expr,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<OmegaConstraint> {
    let inner_constraint = expr_to_mathverse_constraint(inner, whnf_fn).or_else(|| {
        // The inner comparison may only parse after WHNF (instance-carrying
        // `LE.le`/`LT.lt` heads unfold to `Nat.le`/`Nat.lt`). Retry through the
        // provided WHNF function when the direct parse failed.
        let whnf = whnf_fn?;
        let normalized = whnf(inner);
        if normalized != *inner {
            expr_to_mathverse_constraint(&normalized, whnf_fn)
        } else {
            None
        }
    })?;

    match inner_constraint {
        OmegaConstraint::Mod {
            var,
            remainder,
            modulus,
        } => {
            if modulus == 2 {
                // ¬(Even n) ⟺ Odd n: remainder 0 → 1
                // ¬(Odd n) ⟺ Even n: remainder 1 → 0
                Some(OmegaConstraint::Mod {
                    var,
                    remainder: 1 - remainder,
                    modulus: 2,
                })
            } else if remainder == 0 {
                // ¬(a ∣ b) where a ∣ b was parsed as b ≡ 0 (mod a) means b % a ≠ 0
                Some(OmegaConstraint::NotMod { var, modulus })
            } else {
                // ¬(n % m = r) where r ≠ 0: convert to NotLinearMod
                Some(OmegaConstraint::NotLinearMod {
                    expr: LinearExpr::var(var),
                    remainder,
                    modulus,
                })
            }
        }
        OmegaConstraint::LinearMod {
            expr,
            remainder,
            modulus,
        } => {
            // ¬((a + b) % m = r) → NotLinearMod
            Some(OmegaConstraint::NotLinearMod {
                expr,
                remainder,
                modulus,
            })
        }
        OmegaConstraint::NotLinearMod {
            expr,
            remainder,
            modulus,
        } => {
            // ¬(¬((a + b) % m = r)) → LinearMod
            Some(OmegaConstraint::LinearMod {
                expr,
                remainder,
                modulus,
            })
        }
        // Negated linear relations (`¬(a ≤ b)`, `¬(a < b)`, `¬(a = b)`,
        // `¬(a ≠ b)`): `¬P`'s constraint is exactly the negation of `P`'s.
        other => negate_mathverse_constraint(&other),
    }
}

#[derive(Clone, Copy)]
enum ComparisonKind {
    Le,
    Lt,
}

fn parse_direct_binary_comparison(
    expr: &Expr,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<OmegaConstraint> {
    let ExprKind::App(f, rhs) = expr.kind() else {
        return None;
    };
    let ExprKind::App(head, lhs) = f.kind() else {
        return None;
    };
    let ExprKind::Const(name, _) = head.kind() else {
        return None;
    };

    let kind = direct_binary_comparison_kind(&name.to_string())?;
    let lhs_lin = expr_to_linear(lhs, whnf_fn)?;
    let rhs_lin = expr_to_linear(rhs, whnf_fn)?;
    let diff = lhs_lin.sub(&rhs_lin);
    match kind {
        ComparisonKind::Le => Some(OmegaConstraint::Le(diff)),
        ComparisonKind::Lt => Some(OmegaConstraint::Lt(diff)),
    }
}

fn direct_binary_comparison_kind(name: &str) -> Option<ComparisonKind> {
    match name {
        "Nat.le" | "Int.le" | "Rat.le" | "Real.le" => Some(ComparisonKind::Le),
        "Nat.lt" | "Int.lt" | "Rat.lt" | "Real.lt" => Some(ComparisonKind::Lt),
        _ => None,
    }
}

/// Extract a single variable index from an expression (for Even/Odd/Dvd)
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Returns the underlying free-variable index for direct `FVar`
/// expressions and simple coercion/cast wrappers around them.
/// ENSURES: Returns `None` for compound expressions or unsupported wrappers.
/// ENSURES: Recursive descent runs under `stack_safe`.
pub(crate) fn extract_single_var(expr: &Expr) -> Option<usize> {
    stack_safe(|| match expr.kind() {
        ExprKind::FVar(id) => Some(id.as_u64() as usize),
        // Handle simple wrapper applications (like OfNat.ofNat)
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, _) = f.kind() {
                let name_str = name.to_string();
                // Skip type coercions
                if name_str.contains("ofNat") || name_str.contains("cast") {
                    return extract_single_var(arg);
                }
            }
            // Try the argument directly
            extract_single_var(arg)
        }
        _ => None,
    })
}

/// Match a Dvd.dvd application pattern
/// Returns Some((divisor, dividend)) if this is a `a ∣ b` expression
/// REQUIRES: `f2`, `a`, and `b` come from a spine shaped like `((f2 a) b)`.
/// ENSURES: Returns `(a, b)` only when the application head denotes
/// `Dvd.dvd`, possibly with type or instance arguments.
/// ENSURES: Returned expressions are clones of the original divisor and
/// dividend arguments.
fn match_dvd_app(f2: &Expr, a: &Expr, b: &Expr) -> Option<(Expr, Expr)> {
    // Pattern: Dvd.dvd inst a b where inst is the Dvd instance
    if let ExprKind::App(f3, _inst) = f2.kind() {
        if let ExprKind::App(f4, _ty) = f3.kind() {
            if let ExprKind::Const(name, _) = f4.kind() {
                let name_str = name.to_string();
                if name_str == "Dvd.dvd" || name_str.contains("dvd") {
                    return Some((a.clone(), b.clone()));
                }
            }
        }
        // Also try simpler pattern
        if let ExprKind::Const(name, _) = f3.kind() {
            let name_str = name.to_string();
            if name_str == "Dvd.dvd" || name_str.contains("dvd") {
                return Some((a.clone(), b.clone()));
            }
        }
    }
    // Direct Dvd.dvd application
    if let ExprKind::Const(name, _) = f2.kind() {
        let name_str = name.to_string();
        if name_str == "Dvd.dvd" || name_str.contains("dvd") {
            return Some((a.clone(), b.clone()));
        }
    }
    None
}

/// Parse modular equality: `n % m = r` → `n ≡ r (mod m)`
///
/// Recognizes `Eq (HMod.hMod ... n m) r` and desugared `n % m = r` forms.
/// REQUIRES: `expr` is a well-formed equality expression.
/// REQUIRES: When present, `whnf_fn` preserves the semantics of expressions
/// passed to `expr_to_linear`.
/// ENSURES: Returns `Mod` for single-variable congruences and `LinearMod` for
/// general linear congruences with positive modulus and canonical remainder.
/// ENSURES: Returns `None` for non-equalities, unsupported modulo spines, or
/// non-constant/out-of-range modulus and remainder arguments.
fn parse_mod_equality(
    expr: &Expr,
    whnf_fn: Option<&dyn Fn(&Expr) -> Expr>,
) -> Option<OmegaConstraint> {
    // Pattern: `Eq _ (HMod.hMod _ _ _ _ n m) r`
    // The equality is: App (App (App (Const "Eq") ty) lhs) rhs
    // where lhs = HMod.hMod with various args, ending in n and m

    if let ExprKind::App(f, rhs) = expr.kind() {
        if let ExprKind::App(f2, lhs) = f.kind() {
            // Check if this is an Eq
            let is_eq = if let ExprKind::App(f3, _ty) = f2.kind() {
                if let ExprKind::Const(name, _) = f3.kind() {
                    name.to_string().contains("Eq")
                } else {
                    false
                }
            } else {
                false
            };

            if is_eq {
                // Check if lhs is a modulo operation: HMod.hMod
                if let Some((var_expr, modulus_expr)) = match_hmod_app(lhs) {
                    // Extract constant modulus from m
                    if let Some(modulus) = extract_constant(&modulus_expr) {
                        // Extract constant remainder from rhs
                        if let Some(remainder) = extract_constant(rhs) {
                            if modulus > 0 && remainder >= 0 && remainder < modulus {
                                // Try to parse n as a linear expression first
                                // This handles both single variables AND compound expressions
                                if let Some(lin_expr) = expr_to_linear(&var_expr, whnf_fn) {
                                    // If it's a single variable (e.g., x with coefficient 1),
                                    // use the simpler Mod constraint
                                    if lin_expr.coeffs.len() == 1
                                        && lin_expr.constant == 0
                                        && lin_expr.coeffs[0].1 == 1
                                    {
                                        let var = lin_expr.coeffs[0].0;
                                        return Some(OmegaConstraint::Mod {
                                            var,
                                            remainder,
                                            modulus,
                                        });
                                    }
                                    // Otherwise it's a compound expression (a + b, 2*n, etc.)
                                    return Some(OmegaConstraint::LinearMod {
                                        expr: lin_expr,
                                        remainder,
                                        modulus,
                                    });
                                }
                                // Fallback: try extract_single_var for simple FVar cases
                                // that expr_to_linear might not handle
                                if let Some(var) = extract_single_var(&var_expr) {
                                    return Some(OmegaConstraint::Mod {
                                        var,
                                        remainder,
                                        modulus,
                                    });
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

/// Match HMod.hMod application pattern
/// Returns Some((n, m)) if this is `n % m` (HMod.hMod ... n m)
/// REQUIRES: `expr` is a well-formed application spine.
/// ENSURES: Returns `(n, m)` only for `HMod.hMod`/`*.mod` heads with at least
/// two trailing arguments.
/// ENSURES: The returned pair is the final two applied arguments from the
/// matched spine.
pub(crate) fn match_hmod_app(expr: &Expr) -> Option<(Expr, Expr)> {
    // HMod.hMod with full arguments:
    // App (App (App (App (App (App (Const "HMod.hMod") ty1) ty2) ty3) inst) n) m
    // We need to find the function head and extract the last two args (n, m)

    // Try to extract the function name
    let fn_name = get_const_name_from_app(expr);
    if let Some(name) = fn_name {
        let name_str = name.to_string();
        if name_str == "HMod.hMod"
            || name_str == "Nat.mod"
            || name_str == "Int.mod"
            || name_str.ends_with(".hMod")
            || name_str.ends_with(".mod")
        {
            // Extract the last two arguments (n and m)
            if let Some((n, m)) = extract_last_two_args(expr) {
                return Some((n, m));
            }
        }
    }
    None
}

/// Get the constant name from an application chain
/// REQUIRES: `expr` is a well-formed application tree.
/// ENSURES: Returns the head constant name of the application spine, if any.
/// ENSURES: Recursive descent runs under `stack_safe`.
fn get_const_name_from_app(expr: &Expr) -> Option<&Name> {
    stack_safe(|| match expr.kind() {
        ExprKind::Const(name, _) => Some(name),
        ExprKind::App(f, _) => get_const_name_from_app(f),
        _ => None,
    })
}

/// Extract the last two arguments from an application chain
/// REQUIRES: `expr` is a well-formed application spine.
/// ENSURES: Returns the final two applied arguments when the spine depth is at
/// least two.
/// ENSURES: Returns `None` for non-application or single-argument spines.
fn extract_last_two_args(expr: &Expr) -> Option<(Expr, Expr)> {
    // Pattern: App (App ... n) m
    // We want to get n and m
    if let ExprKind::App(f, m) = expr.kind() {
        if let ExprKind::App(_f2, n) = f.kind() {
            return Some((n.as_ref().clone(), m.as_ref().clone()));
        }
    }
    None
}
