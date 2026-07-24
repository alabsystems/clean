// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Real → Int downcast for linarith proof reconstruction (#302, #2493, #2621).
//!
//! Converts `Real.le` hypotheses to `Int.le` via `Real.ofInt_le_to_Int`.
//! Atomic endpoints (`Real.ofNat`, `Real.ofInt`) are handled directly via
//! `Eq.subst(Real.ofNat_eq_ofInt)`. Additive trees (`Real.add`) are
//! normalized recursively in `arith_linarith_real_downcast_additive`.
//!
//! Extracted from `arith_linarith_proof.rs` for file-size compliance.

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{Expr, FVarId};

use super::arith_linarith_real_downcast_additive::{
    mk_eq_mp_prop, mk_real_le_congruence, normalize_real_int_endpoint,
};

/// Downcast a `Real.le` proof to `Int.le` given the Real-sort endpoints.
///
/// Normalizes any `Real.ofNat(n)` endpoints to `Real.ofInt(Int.ofNat n)` via
/// `Eq.subst(Real.ofNat_eq_ofInt)`, extracts `Int` sub-expressions, then
/// applies `Real.ofInt_le_to_Int` to produce `Int.le`.
///
/// Returns `None` if either endpoint is symbolic (not `Real.ofNat`/`Real.ofInt`).
fn downcast_real_le_inner(h: Expr, lhs: &Expr, rhs: &Expr) -> Option<(Expr, Expr, Expr)> {
    let real_ty = Expr::const_(Name::from_string("Real"), vec![]);

    let mk_real_le = |a: &Expr, b: &Expr| -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                        real_ty.clone(),
                    ),
                    Expr::const_(Name::from_string("instLEReal"), vec![]),
                ),
                a.clone(),
            ),
            b.clone(),
        )
    };

    let mut current_h = h;
    let mut current_lhs = lhs.clone();
    let mut current_rhs = rhs.clone();

    // Normalize LHS if Real.ofNat → Real.ofInt(Int.ofNat n)
    if let Some(n) = extract_nat_from_real_ofnat(lhs) {
        let motive = Expr::lam(
            BinderInfo::Default,
            real_ty.clone(),
            mk_real_le(&Expr::bvar(0), &current_rhs),
        );
        current_h = mk_eq_subst_real_normalize(&real_ty, &motive, &n, &current_h);
        current_lhs = mk_real_ofint(Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            n,
        ));
    }

    // Normalize RHS if Real.ofNat → Real.ofInt(Int.ofNat n)
    if let Some(n) = extract_nat_from_real_ofnat(rhs) {
        let motive = Expr::lam(
            BinderInfo::Default,
            real_ty.clone(),
            mk_real_le(&current_lhs, &Expr::bvar(0)),
        );
        current_h = mk_eq_subst_real_normalize(&real_ty, &motive, &n, &current_h);
        current_rhs = mk_real_ofint(Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            n,
        ));
    }

    // Extract Int sub-expressions from normalized Real.ofInt endpoints
    let int_lhs = extract_int_from_real_endpoint(&current_lhs)?;
    let int_rhs = extract_int_from_real_endpoint(&current_rhs)?;

    // Downcast: Real.ofInt_le_to_Int a b h : Int.le a b
    let h_int = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Real.ofInt_le_to_Int"), vec![]),
                int_lhs.clone(),
            ),
            int_rhs.clone(),
        ),
        current_h,
    );

    Some((int_lhs, int_rhs, h_int))
}

/// Downcast a `Real.le` hypothesis (identified by FVarId) to `Int.le`.
///
/// Convenience wrapper for the common case where the proof is a hypothesis.
pub(crate) fn downcast_real_le_to_int(
    fvar: FVarId,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<(Expr, Expr, Expr)> {
    downcast_real_le_inner(Expr::fvar(fvar), lhs, rhs)
}

/// Extract the Int sub-expression from a Real endpoint expression.
///
/// - `Real.ofInt(x)` → `Some(x)`
/// - `Real.ofNat(n)` → `Some(Int.ofNat(n))`
/// - anything else → `None`
fn extract_int_from_real_endpoint(expr: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            let s = name.to_string();
            if s == "Real.ofInt" {
                return Some((**arg).clone());
            }
            if s == "Real.ofNat" {
                return Some(Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    (**arg).clone(),
                ));
            }
        }
    }
    None
}

/// Extract the Nat literal sub-expression from `Real.ofNat(n)`.
fn extract_nat_from_real_ofnat(expr: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Real.ofNat" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

/// Build `Real.ofInt(int_expr)`.
pub(crate) fn mk_real_ofint(int_expr: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

/// Apply `Eq.subst` to normalize a `Real.ofNat(n)` endpoint to `Real.ofInt(Int.ofNat n)`.
///
/// Uses `Real.ofNat_eq_ofInt n : Eq Real (Real.ofNat n) (Real.ofInt (Int.ofNat n))`.
fn mk_eq_subst_real_normalize(real_ty: &Expr, motive: &Expr, ofnat_n: &Expr, h: &Expr) -> Expr {
    let ofnat_expr = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat"), vec![]),
        ofnat_n.clone(),
    );
    let ofint_expr = mk_real_ofint(Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        ofnat_n.clone(),
    ));
    let eq_proof = Expr::app(
        Expr::const_(Name::from_string("Real.ofNat_eq_ofInt"), vec![]),
        ofnat_n.clone(),
    );
    // @Eq.subst.{1} Real motive (Real.ofNat n) (Real.ofInt (Int.ofNat n)) eq_proof h
    let u = Level::succ(Level::zero()); // Real : Type 0 = Sort 1
    let eq_subst = Expr::const_(Name::from_string("Eq.subst"), vec![u]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(Expr::app(eq_subst, real_ty.clone()), motive.clone()),
                    ofnat_expr,
                ),
                ofint_expr,
            ),
            eq_proof,
        ),
        h.clone(),
    )
}

/// Downcast a `Real.le` proof to `Int.le` for integer-valued endpoints (#2621).
///
/// Handles atomic endpoints (`Real.ofInt`, `Real.ofNat`) via the fast path
/// and additive trees (`Real.add`) via recursive normalization to
/// `Real.ofInt(int_expr)` form.
///
/// Tries the atomic path first for performance, then falls back to
/// additive normalization.
pub(crate) fn downcast_integer_valued_real_le_proof_to_int(
    proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<(Expr, Expr, Expr)> {
    // Fast path: atomic endpoints
    if let result @ Some(_) = downcast_real_le_inner(proof.clone(), lhs, rhs) {
        return result;
    }

    // Additive tree normalization
    let norm_lhs = normalize_real_int_endpoint(lhs)?;
    let norm_rhs = normalize_real_int_endpoint(rhs)?;

    let mk_le = |a: &Expr, b: &Expr| -> Expr {
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                        Expr::const_(Name::from_string("Real"), vec![]),
                    ),
                    Expr::const_(Name::from_string("instLEReal"), vec![]),
                ),
                a.clone(),
            ),
            b.clone(),
        )
    };
    let original_prop = mk_le(lhs, rhs);
    let normalized_prop = mk_le(&norm_lhs.real_expr, &norm_rhs.real_expr);
    let prop_eq = mk_real_le_congruence(
        lhs,
        &norm_lhs.real_expr,
        rhs,
        &norm_rhs.real_expr,
        &norm_lhs.eq_proof,
        &norm_rhs.eq_proof,
    );

    let h_norm = mk_eq_mp_prop(&original_prop, &normalized_prop, &prop_eq, proof);

    let h_int = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Real.ofInt_le_to_Int"), vec![]),
                norm_lhs.int_expr.clone(),
            ),
            norm_rhs.int_expr.clone(),
        ),
        h_norm,
    );

    Some((norm_lhs.int_expr, norm_rhs.int_expr, h_int))
}
