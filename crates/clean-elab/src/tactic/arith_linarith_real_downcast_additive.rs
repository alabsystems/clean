// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Additive tree normalization for Real → Int downcast (#2621).
//!
//! Recursively normalizes Real endpoint expressions built from `Real.ofInt`,
//! `Real.ofNat`, `Real.add`, and additive aliases (`HAdd.hAdd`, `Add.add`)
//! into `Real.ofInt(int_expr)` form with equality proofs via
//! `congrArg`/`congr`/`Eq.trans` and `Eq.symm(Real.ofInt_add)`.
//!
//! Split from `arith_linarith_real_downcast.rs` for file-size compliance.

use clean_kernel::expr::{BinderInfo, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::Expr;

use super::arith_linarith_real_downcast::mk_real_ofint;

// ---------------------------------------------------------------------------
// Equality proof builders (Real at universe 1)
// ---------------------------------------------------------------------------

fn u1() -> Level {
    Level::succ(Level::zero())
}

fn mk_eq_refl_real(val: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Eq.refl"), vec![u1()]),
            Expr::const_(Name::from_string("Real"), vec![]),
        ),
        val.clone(),
    )
}

fn mk_eq_symm_real(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.symm"), vec![u1()]),
                    Expr::const_(Name::from_string("Real"), vec![]),
                ),
                a.clone(),
            ),
            b.clone(),
        ),
        h.clone(),
    )
}

fn mk_eq_trans_real(a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("Eq.trans"), vec![u1()]),
                            Expr::const_(Name::from_string("Real"), vec![]),
                        ),
                        a.clone(),
                    ),
                    b.clone(),
                ),
                c.clone(),
            ),
            h1.clone(),
        ),
        h2.clone(),
    )
}

fn mk_congr_arg_11(alpha: &Expr, beta: &Expr, a1: &Expr, a2: &Expr, f: &Expr, h: &Expr) -> Expr {
    let u = u1();
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::const_(Name::from_string("congrArg"), vec![u.clone(), u]),
                            alpha.clone(),
                        ),
                        beta.clone(),
                    ),
                    a1.clone(),
                ),
                a2.clone(),
            ),
            f.clone(),
        ),
        h.clone(),
    )
}

fn mk_congr_11(
    alpha: &Expr,
    beta: &Expr,
    f1: &Expr,
    f2: &Expr,
    a1: &Expr,
    a2: &Expr,
    hf: &Expr,
    ha: &Expr,
) -> Expr {
    let u = u1();
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::app(
                        Expr::app(
                            Expr::app(
                                Expr::app(
                                    Expr::const_(Name::from_string("congr"), vec![u.clone(), u]),
                                    alpha.clone(),
                                ),
                                beta.clone(),
                            ),
                            f1.clone(),
                        ),
                        f2.clone(),
                    ),
                    a1.clone(),
                ),
                a2.clone(),
            ),
            hf.clone(),
        ),
        ha.clone(),
    )
}

/// `@Eq.mp.{0} α β h a : β` — propositional transport.
pub(crate) fn mk_eq_mp_prop(alpha: &Expr, beta: &Expr, h: &Expr, a: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Eq.mp"), vec![Level::zero()]),
                    alpha.clone(),
                ),
                beta.clone(),
            ),
            h.clone(),
        ),
        a.clone(),
    )
}

// ---------------------------------------------------------------------------
// Additive tree helpers
// ---------------------------------------------------------------------------

fn as_raw_real_add(expr: &Expr) -> Option<(Expr, Expr)> {
    let expr = expr.strip_mdata();
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }
    if let ExprKind::Const(name, _) = expr.get_app_fn().strip_mdata().kind() {
        if name.to_string() == "Real.add" {
            let arity = args.len();
            return Some((args[arity - 2].clone(), args[arity - 1].clone()));
        }
    }
    None
}

fn as_real_add_alias(expr: &Expr) -> Option<(Expr, Expr)> {
    let expr = expr.strip_mdata();
    let args = expr.get_app_args();
    if args.len() < 2 {
        return None;
    }
    if let ExprKind::Const(name, _) = expr.get_app_fn().strip_mdata().kind() {
        return match name.to_string().as_str() {
            "HAdd.hAdd" if args.len() >= 6 => {
                Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()))
            }
            "Add.add" if args.len() >= 2 => {
                Some((args[args.len() - 2].clone(), args[args.len() - 1].clone()))
            }
            _ => None,
        };
    }
    None
}

fn decompose_real_add(expr: &Expr) -> Option<(Expr, Expr, Expr, Option<Expr>)> {
    let expr = expr.strip_mdata();
    if let Some((lhs, rhs)) = as_raw_real_add(expr) {
        return Some((lhs, rhs, expr.clone(), None));
    }
    if let Some((lhs, rhs)) = as_real_add_alias(expr) {
        let raw_expr = mk_real_add_expr(&lhs, &rhs);
        // `HAdd.hAdd ...` / `Add.add ...` reduce definitionally to `Real.add`.
        let raw_intro = mk_eq_refl_real(&raw_expr);
        return Some((lhs, rhs, raw_expr, Some(raw_intro)));
    }
    None
}

fn mk_real_add_expr(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.add"), vec![]),
            a.clone(),
        ),
        b.clone(),
    )
}

fn mk_int_add_expr(a: &Expr, b: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Int.add"), vec![]),
            a.clone(),
        ),
        b.clone(),
    )
}

// ---------------------------------------------------------------------------
// Recursive endpoint normalization
// ---------------------------------------------------------------------------

/// Intermediate result: a Real endpoint normalized to `Real.ofInt(int_expr)`.
pub(crate) struct NormalizedRealInt {
    pub(crate) int_expr: Expr,
    pub(crate) real_expr: Expr,
    pub(crate) eq_proof: Expr,
}

/// Normalize a Real additive node given already-normalized children.
fn normalize_real_add_to_ofint(
    original_expr: &Expr,
    raw_expr: &Expr,
    raw_intro: Option<&Expr>,
    child_a: &Expr,
    child_b: &Expr,
    norm_a: &NormalizedRealInt,
    norm_b: &NormalizedRealInt,
) -> NormalizedRealInt {
    let combined_int = mk_int_add_expr(&norm_a.int_expr, &norm_b.int_expr);
    let real_expr = mk_real_ofint(combined_int.clone());
    let real = Expr::const_(Name::from_string("Real"), vec![]);

    // Step 1: Real.add(child_a, child_b) = Real.add(norm_a.real, norm_b.real)
    let real_add = Expr::const_(Name::from_string("Real.add"), vec![]);
    let real_to_real = Expr::pi(BinderInfo::Default, real.clone(), real.clone());
    let lhs_eq = mk_congr_arg_11(
        &real,
        &real_to_real,
        child_a,
        &norm_a.real_expr,
        &real_add,
        &norm_a.eq_proof,
    );
    let mid = mk_real_add_expr(&norm_a.real_expr, &norm_b.real_expr);
    let step1 = mk_congr_11(
        &real,
        &real,
        &Expr::app(real_add.clone(), child_a.clone()),
        &Expr::app(real_add, norm_a.real_expr.clone()),
        child_b,
        &norm_b.real_expr,
        &lhs_eq,
        &norm_b.eq_proof,
    );

    // Step 2: via Eq.symm(Real.ofInt_add)
    let ofint_add = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.ofInt_add"), vec![]),
            norm_a.int_expr.clone(),
        ),
        norm_b.int_expr.clone(),
    );
    let step2 = mk_eq_symm_real(&real_expr, &mid, &ofint_add);

    let step1 = if let Some(raw_intro) = raw_intro {
        mk_eq_trans_real(original_expr, raw_expr, &mid, raw_intro, &step1)
    } else {
        step1
    };

    let eq_proof = mk_eq_trans_real(original_expr, &mid, &real_expr, &step1, &step2);

    NormalizedRealInt {
        int_expr: combined_int,
        real_expr,
        eq_proof,
    }
}

/// Recursively normalize a Real endpoint to `Real.ofInt(int_expr)` form.
///
/// Handles: `Real.ofInt(e)`, `Real.ofNat(n)`, `Real.add(a, b)`,
/// `HAdd.hAdd ... a b`, and `Add.add a b`.
/// Returns `None` for expressions outside this bounded family.
pub(crate) fn normalize_real_int_endpoint(expr: &Expr) -> Option<NormalizedRealInt> {
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.kind() {
            let s = name.to_string();
            if s == "Real.ofInt" {
                return Some(NormalizedRealInt {
                    int_expr: (**arg).clone(),
                    real_expr: expr.clone(),
                    eq_proof: mk_eq_refl_real(expr),
                });
            }
            if s == "Real.ofNat" {
                let int_expr = Expr::app(
                    Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                    (**arg).clone(),
                );
                let real_expr = mk_real_ofint(int_expr.clone());
                let eq_proof = Expr::app(
                    Expr::const_(Name::from_string("Real.ofNat_eq_ofInt"), vec![]),
                    (**arg).clone(),
                );
                return Some(NormalizedRealInt {
                    int_expr,
                    real_expr,
                    eq_proof,
                });
            }
        }
    }

    let (child_a, child_b, raw_expr, raw_intro) = decompose_real_add(expr)?;
    let norm_a = normalize_real_int_endpoint(&child_a)?;
    let norm_b = normalize_real_int_endpoint(&child_b)?;
    Some(normalize_real_add_to_ofint(
        expr,
        &raw_expr,
        raw_intro.as_ref(),
        &child_a,
        &child_b,
        &norm_a,
        &norm_b,
    ))
}

/// Build proposition equality for LE.le when both endpoints change.
pub(crate) fn mk_real_le_congruence(
    lhs_from: &Expr,
    lhs_to: &Expr,
    rhs_from: &Expr,
    rhs_to: &Expr,
    lhs_eq: &Expr,
    rhs_eq: &Expr,
) -> Expr {
    let real = Expr::const_(Name::from_string("Real"), vec![]);
    let prop = Expr::prop();
    let real_to_prop = Expr::pi(BinderInfo::Default, real.clone(), prop.clone());
    let rel = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("LE.le"), vec![Level::zero()]),
            real.clone(),
        ),
        Expr::const_(Name::from_string("instLEReal"), vec![]),
    );
    let partial_eq = mk_congr_arg_11(&real, &real_to_prop, lhs_from, lhs_to, &rel, lhs_eq);
    mk_congr_11(
        &real,
        &prop,
        &Expr::app(rel.clone(), lhs_from.clone()),
        &Expr::app(rel, lhs_to.clone()),
        rhs_from,
        rhs_to,
        &partial_eq,
        rhs_eq,
    )
}
