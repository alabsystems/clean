// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Recursive Real → `Real.ofInt(...)` normalization pipeline (#2599).
//!
//! Normalizes Real-sort endpoint expressions into `Real.ofInt(int_expr)` form
//! by recursively handling `Real.ofInt`, `Real.ofNat`, `Real.add`, and
//! `HAdd.hAdd`/`Add.add` aliases. Each step carries an equality proof
//! through `congr_arg`/`congr`/`Eq.trans` chains.

use super::expr_builders_arith::CmpOp;
use super::theory_lemma_lra_additive::mk_int_add;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

// ---------------------------------------------------------------------------
// Small builder helpers
// ---------------------------------------------------------------------------

fn mk_real_ofint_expr(int_expr: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        int_expr,
    )
}

fn mk_real_ty() -> Expr {
    Expr::const_(Name::from_string("Real"), vec![])
}

fn mk_real_eq_refl(val: &Expr) -> Expr {
    crate::bridge::eq_proof_builders::mk_eq_refl(&Level::succ(Level::zero()), &mk_real_ty(), val)
}

fn mk_real_to_real_type() -> Expr {
    let real_ty = mk_real_ty();
    Expr::pi(BinderInfo::Default, real_ty.clone(), real_ty)
}

/// Extract the Nat literal from a `Real.ofNat(NatLit(n))` expression.
fn extract_nat_from_real_ofnat(expr: &Expr) -> Option<Expr> {
    let expr = expr.strip_mdata();
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.strip_mdata().kind() {
            if name.to_string() == "Real.ofNat" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

/// Build `@Real.ofNat_eq_ofInt n : Eq Real (Real.ofNat n) (Real.ofInt (Int.ofNat n))`.
fn mk_real_ofnat_eq_ofint(n: &Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Real.ofNat_eq_ofInt"), vec![]),
        n.clone(),
    )
}

/// `Real.add(a, b)` in canonical 2-arg form (for axiom references).
fn mk_real_add_canonical(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.add"), vec![]),
            a.clone(),
        ),
        b.clone(),
    )
}

/// `@Real.ofInt_add m n` — cast-movement equality for Real.add over Real.ofInt.
fn mk_real_ofint_add(m: &Expr, n: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt_add"), vec![]),
            m.clone(),
        ),
        n.clone(),
    )
}

// ---------------------------------------------------------------------------
// Comparison-proposition and congruence builders
// ---------------------------------------------------------------------------

fn mk_real_cmp_prop(op: CmpOp, lhs: &Expr, rhs: &Expr) -> Expr {
    let (cmp_name, cmp_inst) = match op {
        CmpOp::Le => ("LE.le", "instLEReal"),
        CmpOp::Lt => ("LT.lt", "instLTReal"),
    };
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string(cmp_name), vec![Level::zero()]),
                    mk_real_ty(),
                ),
                Expr::const_(Name::from_string(cmp_inst), vec![]),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

fn mk_real_add_apply_eq(
    lhs_from: &Expr,
    lhs_to: &Expr,
    rhs_from: &Expr,
    rhs_to: &Expr,
    lhs_eq: &Expr,
    rhs_eq: &Expr,
) -> Expr {
    let real_ty = mk_real_ty();
    let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);
    let u = Level::succ(Level::zero());
    let partial_eq = crate::bridge::eq_proof_builders::mk_congr_arg(
        &u,
        &u,
        &real_ty,
        &mk_real_to_real_type(),
        lhs_from,
        lhs_to,
        &real_add,
        lhs_eq,
    );

    crate::bridge::eq_proof_builders::mk_congr(
        &u,
        &u,
        &real_ty,
        &real_ty,
        &Expr::app(real_add.clone(), lhs_from.clone()),
        &Expr::app(real_add, lhs_to.clone()),
        rhs_from,
        rhs_to,
        &partial_eq,
        rhs_eq,
    )
}

fn mk_real_cmp_apply_eq(
    op: CmpOp,
    lhs_from: &Expr,
    lhs_to: &Expr,
    rhs_from: &Expr,
    rhs_to: &Expr,
    lhs_eq: &Expr,
    rhs_eq: &Expr,
) -> Expr {
    let real_ty = mk_real_ty();
    let prop_ty = Expr::prop();
    let u = Level::succ(Level::zero());
    let rel = match op {
        CmpOp::Le => Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
                real_ty.clone(),
            ),
            Expr::const_(Name::from_string("instLEReal"), vec![]),
        ),
        CmpOp::Lt => Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("LT.lt"), vec![Level::zero()]),
                real_ty.clone(),
            ),
            Expr::const_(Name::from_string("instLTReal"), vec![]),
        ),
    };
    // rel : Real → Real → Prop, so after one application the intermediate
    // codomain is (Real → Prop) : Sort 1.  Both congruence steps therefore
    // use v = 1:
    //   Step 1 (congrArg): β = Real → Prop, v = 1
    //   Step 2 (congr):    β = Prop : Sort 1, v = 1
    let v = Level::succ(Level::zero());
    // Intermediate codomain type: Real → Prop (matching mk_real_to_real_type
    // pattern used in mk_real_add_apply_eq).
    let real_to_prop_ty = Expr::pi(BinderInfo::Default, real_ty.clone(), prop_ty.clone());
    let partial_eq = crate::bridge::eq_proof_builders::mk_congr_arg(
        &u,
        &v,
        &real_ty,
        &real_to_prop_ty,
        lhs_from,
        lhs_to,
        &rel,
        lhs_eq,
    );

    crate::bridge::eq_proof_builders::mk_congr(
        &u,
        &v,
        &real_ty,
        &prop_ty,
        &Expr::app(rel.clone(), lhs_from.clone()),
        &Expr::app(rel, lhs_to.clone()),
        rhs_from,
        rhs_to,
        &partial_eq,
        rhs_eq,
    )
}

// ---------------------------------------------------------------------------
// Real.add decomposition helpers
// ---------------------------------------------------------------------------

fn as_raw_real_add(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let expr = expr.strip_mdata();
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }
    if let ExprKind::Const(name, _) = expr.get_app_fn().strip_mdata().kind() {
        if name.to_string() == "Real.add" {
            let arity = args.len();
            return Some((args[arity - 2], args[arity - 1]));
        }
    }
    None
}

fn as_alias_real_add(expr: &Expr) -> Option<(&Expr, &Expr)> {
    let expr = expr.strip_mdata();
    let fn_head = expr.get_app_fn().strip_mdata();
    if let ExprKind::Const(name, _) = fn_head.kind() {
        let args = expr.get_app_args();
        return match name.to_string().as_str() {
            "HAdd.hAdd" if args.len() >= 6 => Some((args[args.len() - 2], args[args.len() - 1])),
            "Add.add" if args.len() >= 2 => Some((args[args.len() - 2], args[args.len() - 1])),
            _ => None,
        };
    }
    None
}

/// Decompose Real addition into canonical `Real.add(lhs, rhs)`.
fn decompose_real_add(expr: &Expr) -> Option<(&Expr, &Expr, Expr, Option<Expr>)> {
    let expr = expr.strip_mdata();
    if let Some((lhs, rhs)) = as_raw_real_add(expr) {
        return Some((lhs, rhs, expr.clone(), None));
    }
    if let Some((lhs, rhs)) = as_alias_real_add(expr) {
        let raw_expr = mk_real_add_canonical(lhs, rhs);
        let raw_intro = mk_real_eq_refl(&raw_expr);
        return Some((lhs, rhs, raw_expr, Some(raw_intro)));
    }
    None
}

/// Extract the Int argument from `Real.ofInt(x)` only (not Real.ofNat).
fn extract_ofint_inner(expr: &Expr) -> Option<Expr> {
    let expr = expr.strip_mdata();
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.strip_mdata().kind() {
            if name.to_string() == "Real.ofInt" {
                return Some((**arg).clone());
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Recursive normalization pipeline
// ---------------------------------------------------------------------------

#[derive(Clone)]
struct NormalizedRealOfInt {
    int_expr: Expr,
    real_expr: Expr,
    eq_proof: Expr,
}

/// Recursively normalize a Real endpoint into `Real.ofInt _`.
fn normalize_real_endpoint_to_ofint(expr: &Expr) -> Option<NormalizedRealOfInt> {
    crate::bridge::stack_safe(|| {
        let expr = expr.strip_mdata();

        if let Some(int_expr) = extract_ofint_inner(expr) {
            return Some(NormalizedRealOfInt {
                real_expr: mk_real_ofint_expr(int_expr.clone()),
                int_expr,
                eq_proof: mk_real_eq_refl(expr),
            });
        }

        if let Some(n) = extract_nat_from_real_ofnat(expr) {
            let int_expr = Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                n.clone(),
            );
            return Some(NormalizedRealOfInt {
                real_expr: mk_real_ofint_expr(int_expr.clone()),
                int_expr,
                eq_proof: mk_real_ofnat_eq_ofint(&n),
            });
        }

        let (lhs, rhs, raw_expr, raw_intro) = decompose_real_add(expr)?;
        let lhs_norm = normalize_real_endpoint_to_ofint(lhs)?;
        let rhs_norm = normalize_real_endpoint_to_ofint(rhs)?;
        let mid = mk_real_add_canonical(&lhs_norm.real_expr, &rhs_norm.real_expr);
        let step1 = mk_real_add_apply_eq(
            lhs,
            &lhs_norm.real_expr,
            rhs,
            &rhs_norm.real_expr,
            &lhs_norm.eq_proof,
            &rhs_norm.eq_proof,
        );
        let step1 = if let Some(raw_intro) = raw_intro {
            crate::bridge::eq_proof_builders::mk_eq_trans(
                &Level::succ(Level::zero()),
                &mk_real_ty(),
                expr,
                &raw_expr,
                &mid,
                &raw_intro,
                &step1,
            )
        } else {
            step1
        };

        let int_expr = mk_int_add(&lhs_norm.int_expr, &rhs_norm.int_expr);
        let real_expr = mk_real_ofint_expr(int_expr.clone());
        let add_eq = mk_real_ofint_add(&lhs_norm.int_expr, &rhs_norm.int_expr);
        let add_eq_sym = crate::bridge::eq_proof_builders::mk_eq_symm(
            &Level::succ(Level::zero()),
            &mk_real_ty(),
            &real_expr,
            &mid,
            &add_eq,
        );
        let eq_proof = crate::bridge::eq_proof_builders::mk_eq_trans(
            &Level::succ(Level::zero()),
            &mk_real_ty(),
            expr,
            &mid,
            &real_expr,
            &step1,
            &add_eq_sym,
        );

        Some(NormalizedRealOfInt {
            int_expr,
            real_expr,
            eq_proof,
        })
    })
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

/// Normalize a Real comparison proof so both endpoints are `Real.ofInt _`.
///
/// Returns `(lhs_norm, rhs_norm, h_norm)` where `h_norm` proves the same
/// comparison as `h_real`, but over the normalized endpoints.
pub(crate) fn normalize_real_cmp_proof_to_ofint(
    op: CmpOp,
    lhs_expr: &Expr,
    rhs_expr: &Expr,
    h_real: &Expr,
) -> Option<(Expr, Expr, Expr)> {
    let lhs_norm = normalize_real_endpoint_to_ofint(lhs_expr)?;
    let rhs_norm = normalize_real_endpoint_to_ofint(rhs_expr)?;
    let original_prop = mk_real_cmp_prop(op, lhs_expr, rhs_expr);
    let normalized_prop = mk_real_cmp_prop(op, &lhs_norm.real_expr, &rhs_norm.real_expr);
    let prop_eq = mk_real_cmp_apply_eq(
        op,
        lhs_expr,
        &lhs_norm.real_expr,
        rhs_expr,
        &rhs_norm.real_expr,
        &lhs_norm.eq_proof,
        &rhs_norm.eq_proof,
    );
    let h_norm = crate::bridge::eq_proof_builders::mk_eq_mp(
        &Level::zero(),
        &original_prop,
        &normalized_prop,
        &prop_eq,
        h_real,
    );

    Some((lhs_norm.real_expr, rhs_norm.real_expr, h_norm))
}
