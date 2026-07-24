// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rat → Int downcast for linarith proof reconstruction (#3367).
//!
//! Converts proofs of `LE.le Rat instLERat (Rat.ofInt a) (Rat.ofInt b)` (which
//! is definitionally `Rat.le (Rat.ofInt a) (Rat.ofInt b)` because `instLERat`
//! is a reducible `Definition` projecting to `Rat.le`) into proofs of
//! `Int.le a b` via the registered cast-transfer axiom
//! `Int.cast_le_prop : ∀ a b : Int, Eq Prop (Int.le a b)
//! (Rat.le (Rat.ofInt a) (Rat.ofInt b))` (see `cast_lemmas.rs`).
//!
//! The downcast uses `Eq.mpr : {α β : Sort u} → Eq α β → β → α` to transport
//! the rational proof across the proposition equality, producing an
//! `Int.le a b` proof that the existing contradiction-close path
//! (`try_close_contradictory_int_le`) can evaluate against concrete endpoints.
//!
//! This path covers the acceptance criterion "Farkas-style combinations of
//! linear inequalities over Rat" for integer-valued Rat endpoints, which is
//! the form gamma-crown proofs emit (C001 triangle inequalities,
//! C008 bound propagation).

use clean_kernel::expr::ExprKind;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

/// Extract the `Int` sub-expression from a `Rat.ofInt(e)` endpoint.
///
/// Returns `Some(e)` for `Rat.ofInt(e)`, `None` otherwise.
fn extract_int_from_rat_endpoint(expr: &Expr) -> Option<Expr> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            if name.to_string() == "Rat.ofInt" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

/// Build `Eq.mpr.{0} α β h_eq b`, yielding a proof of `α` from `h_eq : Eq Prop α β`
/// and `b : β`.
fn mk_eq_mpr_prop(alpha: &Expr, beta: &Expr, h_eq: &Expr, b: &Expr) -> Expr {
    let eq_mpr = Expr::const_(Name::from_string("Eq.mpr"), vec![Level::zero()]);
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(eq_mpr, alpha.clone()), beta.clone()),
            h_eq.clone(),
        ),
        b.clone(),
    )
}

/// Downcast a `Rat.le` (or def-eq `LE.le Rat instLERat`) proof to `Int.le`
/// when both endpoints are `Rat.ofInt(int_expr)`.
///
/// Given:
/// - `proof : LE.le Rat instLERat (Rat.ofInt a) (Rat.ofInt b)`
///   (kernel-def-eq to `Rat.le (Rat.ofInt a) (Rat.ofInt b)`)
/// - `lhs = Rat.ofInt a`
/// - `rhs = Rat.ofInt b`
///
/// Produces `(a, b, Int.le a b proof term)` by transporting via
/// `Int.cast_le_prop a b : Eq Prop (Int.le a b) (Rat.le (Rat.ofInt a) (Rat.ofInt b))`
/// using `Eq.mpr`.
///
/// REQUIRES: `proof` has a type kernel-def-eq to `Rat.le lhs rhs`
/// REQUIRES: `Int.cast_le_prop` is registered in the environment
///           (via `env.init_cast_simp_lemmas()`)
/// ENSURES: On `Some((int_lhs, int_rhs, int_proof))`,
///          `int_proof` has type `Int.le int_lhs int_rhs`
/// ENSURES: On `None`, either endpoint is not of the form `Rat.ofInt(_)`
pub(crate) fn downcast_integer_valued_rat_le_proof_to_int(
    proof: &Expr,
    lhs: &Expr,
    rhs: &Expr,
) -> Option<(Expr, Expr, Expr)> {
    let int_lhs = extract_int_from_rat_endpoint(lhs)?;
    let int_rhs = extract_int_from_rat_endpoint(rhs)?;

    // α = Int.le a b
    let int_le = Expr::const_(Name::from_string("Int.le"), vec![]);
    let alpha = Expr::app(Expr::app(int_le, int_lhs.clone()), int_rhs.clone());

    // β = Rat.le (Rat.ofInt a) (Rat.ofInt b)
    let rat_le = Expr::const_(Name::from_string("Rat.le"), vec![]);
    let beta = Expr::app(Expr::app(rat_le, lhs.clone()), rhs.clone());

    // h_eq = Int.cast_le_prop a b : Eq Prop α β
    let h_eq = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.cast_le_prop"), vec![]),
            int_lhs.clone(),
        ),
        int_rhs.clone(),
    );

    let int_proof = mk_eq_mpr_prop(&alpha, &beta, &h_eq, proof);

    Some((int_lhs, int_rhs, int_proof))
}

#[cfg(test)]
mod tests {
    use super::*;
    use clean_kernel::FVarId;

    #[test]
    fn test_extract_int_from_rat_endpoint_ofint() {
        let inner = Expr::const_(Name::from_string("X"), vec![]);
        let rat_ofint = Expr::app(
            Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
            inner.clone(),
        );
        assert_eq!(extract_int_from_rat_endpoint(&rat_ofint), Some(inner));
    }

    #[test]
    fn test_extract_int_from_rat_endpoint_rejects_non_ofint() {
        let other = Expr::app(
            Expr::const_(Name::from_string("Rat.mk"), vec![]),
            Expr::nat_lit(1),
        );
        assert!(extract_int_from_rat_endpoint(&other).is_none());
    }

    #[test]
    fn test_downcast_rejects_non_ofint_lhs() {
        let proof = Expr::fvar(FVarId::new(0));
        let non_ofint = Expr::const_(Name::from_string("x"), vec![]);
        let rat_ofint = Expr::app(
            Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
            Expr::const_(Name::from_string("y"), vec![]),
        );
        assert!(
            downcast_integer_valued_rat_le_proof_to_int(&proof, &non_ofint, &rat_ofint).is_none()
        );
    }

    #[test]
    fn test_downcast_structure() {
        let proof = Expr::fvar(FVarId::new(42));
        let a_int = Expr::const_(Name::from_string("a"), vec![]);
        let b_int = Expr::const_(Name::from_string("b"), vec![]);
        let lhs = Expr::app(
            Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
            a_int.clone(),
        );
        let rhs = Expr::app(
            Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
            b_int.clone(),
        );

        let (int_lhs, int_rhs, int_proof) =
            downcast_integer_valued_rat_le_proof_to_int(&proof, &lhs, &rhs)
                .expect("Rat.ofInt endpoints should downcast");
        assert_eq!(int_lhs, a_int);
        assert_eq!(int_rhs, b_int);
        // Verify the head of int_proof is Eq.mpr.
        let head = int_proof.get_app_fn();
        match head.kind() {
            ExprKind::Const(name, _) => {
                assert_eq!(name.to_string(), "Eq.mpr");
            }
            _ => panic!("int_proof head should be Eq.mpr, got {head:?}"),
        }
    }
}
