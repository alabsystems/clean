// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use clean_kernel::name::Name;
use clean_kernel::tc::whnf_proof::{CongrArgArgs, EqProofBuilder};
use clean_kernel::{Expr, ExprKind, Level};

use super::super::polynomial::VarMap;
use super::super::{ring_nf, Goal, ProofState};
use super::preprocess::parse_fvar_name;
use super::types::{EqAcc, Rational, RationalPolynomial};

pub(super) fn rational_polynomial_to_expr(
    poly: &RationalPolynomial,
    poly_var_map: &VarMap,
    alpha: &Expr,
) -> Option<Expr> {
    if poly.is_zero() {
        return make_zero_expr(alpha);
    }

    let mut sum: Option<Expr> = None;
    for (mono, coeff) in &poly.terms {
        let term = rational_term_to_expr(mono, *coeff, poly_var_map, alpha)?;
        sum = Some(match sum {
            None => term,
            Some(existing) => make_add_app(alpha, &existing, &term)?,
        });
    }
    sum.or_else(|| make_zero_expr(alpha))
}

fn rational_term_to_expr(
    mono: &super::types::Monomial,
    coeff: Rational,
    poly_var_map: &VarMap,
    alpha: &Expr,
) -> Option<Expr> {
    let coeff_expr = make_scalar_expr(alpha, coeff)?;
    if mono.is_empty() {
        return Some(coeff_expr);
    }

    let mut monomial_expr: Option<Expr> = None;
    for (var_idx, exp) in mono {
        let var_name = poly_var_map.name(*var_idx)?;
        let var_expr = expr_for_polynomial_var(var_name)?;
        for _ in 0..*exp {
            monomial_expr = Some(match monomial_expr {
                None => var_expr.clone(),
                Some(ref existing) => make_mul_app(alpha, existing, &var_expr)?,
            });
        }
    }
    let monomial_expr = monomial_expr?;

    if coeff == Rational::one() {
        Some(monomial_expr)
    } else {
        make_mul_app(alpha, &coeff_expr, &monomial_expr)
    }
}

fn expr_for_polynomial_var(name: &str) -> Option<Expr> {
    if let Some(fvar) = parse_fvar_name(name) {
        return Some(Expr::fvar(fvar));
    }

    Some(Expr::const_(Name::from_string(name), vec![]))
}

pub(super) fn make_eq_type(alpha: &Expr, lhs: &Expr, rhs: &Expr, u: &Level) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![u.clone()]),
                alpha.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}

pub(super) fn make_add_right_lambda(alpha: &Expr, lhs_fixed: &Expr) -> Option<Expr> {
    Some(Expr::lam(
        clean_kernel::BinderInfo::Default,
        alpha.clone(),
        make_add_app(alpha, lhs_fixed, &Expr::bvar(0))?,
    ))
}

fn make_add_left_lambda(alpha: &Expr, rhs_fixed: &Expr) -> Option<Expr> {
    Some(Expr::lam(
        clean_kernel::BinderInfo::Default,
        alpha.clone(),
        make_add_app(alpha, &Expr::bvar(0), rhs_fixed)?,
    ))
}

fn make_mul_lambda(alpha: &Expr, coeff: &Expr) -> Option<Expr> {
    Some(Expr::lam(
        clean_kernel::BinderInfo::Default,
        alpha.clone(),
        make_mul_app(alpha, coeff, &Expr::bvar(0))?,
    ))
}

pub(super) fn make_add_app(alpha: &Expr, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let op_name = match carrier_name(alpha)? {
        "Nat" => "Nat.add",
        "Int" => "Int.add",
        "Rat" => "Rat.add",
        "Real" => "Real.add",
        _ => return None,
    };
    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(op_name), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    ))
}

fn make_mul_app(alpha: &Expr, lhs: &Expr, rhs: &Expr) -> Option<Expr> {
    let op_name = match carrier_name(alpha)? {
        "Nat" => "Nat.mul",
        "Int" => "Int.mul",
        "Rat" => "Rat.mul",
        "Real" => "Real.mul",
        _ => return None,
    };
    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(op_name), vec![]),
            lhs.clone(),
        ),
        rhs.clone(),
    ))
}

fn make_zero_expr(alpha: &Expr) -> Option<Expr> {
    make_scalar_expr(alpha, Rational::new(0, 1))
}

fn make_scalar_expr(alpha: &Expr, coeff: Rational) -> Option<Expr> {
    if coeff.is_zero() {
        return match carrier_name(alpha)? {
            "Nat" => Some(Expr::nat_lit(0)),
            "Int" => Some(Expr::const_(Name::from_string("Int.zero"), vec![])),
            "Rat" => Some(Expr::const_(Name::from_string("Rat.zero"), vec![])),
            "Real" => Some(Expr::const_(Name::from_string("Real.zero"), vec![])),
            _ => None,
        };
    }

    match carrier_name(alpha)? {
        "Nat" if coeff.den == 1 && coeff.num >= 0 => {
            Some(Expr::nat_lit(u64::try_from(coeff.num).ok()?))
        }
        "Int" if coeff.den == 1 => Some(make_int_expr(i64::try_from(coeff.num).ok()?)),
        "Rat" => make_rat_expr(coeff),
        "Real" => make_real_expr(coeff),
        _ => None,
    }
}

fn make_int_expr(n: i64) -> Expr {
    if n >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(n as u64),
        )
    } else {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n.unsigned_abs() - 1),
        )
    }
}

fn make_rat_expr(coeff: Rational) -> Option<Expr> {
    let numerator = Expr::app(
        Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
        make_int_expr(i64::try_from(coeff.num).ok()?),
    );
    if coeff.den == 1 {
        return Some(numerator);
    }
    let denominator = Expr::app(
        Expr::const_(Name::from_string("Rat.ofInt"), vec![]),
        make_int_expr(i64::try_from(coeff.den).ok()?),
    );
    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Rat.div"), vec![]),
            numerator,
        ),
        denominator,
    ))
}

fn make_real_expr(coeff: Rational) -> Option<Expr> {
    let numerator = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        make_int_expr(i64::try_from(coeff.num).ok()?),
    );
    if coeff.den == 1 {
        return Some(numerator);
    }
    let denominator = Expr::app(
        Expr::const_(Name::from_string("Real.ofInt"), vec![]),
        make_int_expr(i64::try_from(coeff.den).ok()?),
    );
    Some(Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Real.div"), vec![]),
            numerator,
        ),
        denominator,
    ))
}

fn carrier_name(alpha: &Expr) -> Option<&'static str> {
    match alpha.kind() {
        ExprKind::Const(name, _) => match name.to_string().as_str() {
            "Nat" => Some("Nat"),
            "Int" => Some("Int"),
            "Rat" => Some("Rat"),
            "Real" => Some("Real"),
            _ => None,
        },
        _ => None,
    }
}

impl EqAcc {
    pub(super) fn from_hypothesis(
        alpha: &Expr,
        u: &Level,
        hyp_fvar: &Expr,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Option<Self> {
        Some(Self {
            alpha: alpha.clone(),
            u: u.clone(),
            lhs: lhs.clone(),
            rhs: rhs.clone(),
            proof: hyp_fvar.clone(),
        })
    }

    pub(super) fn from_scaled_expr(
        alpha: &Expr,
        u: &Level,
        hyp_fvar: &Expr,
        lhs: &Expr,
        rhs: &Expr,
        coeff_expr: &Expr,
    ) -> Option<Self> {
        let proof = EqProofBuilder::mk_congr_arg(CongrArgArgs {
            u: u.clone(),
            v: u.clone(),
            alpha: alpha.clone(),
            beta: alpha.clone(),
            f: make_mul_lambda(alpha, coeff_expr)?,
            a1: lhs.clone(),
            a2: rhs.clone(),
            h: hyp_fvar.clone(),
        });

        Some(Self {
            alpha: alpha.clone(),
            u: u.clone(),
            lhs: make_mul_app(alpha, coeff_expr, lhs)?,
            rhs: make_mul_app(alpha, coeff_expr, rhs)?,
            proof,
        })
    }

    pub(super) fn combine(self, next: EqAcc) -> Option<EqAcc> {
        let step1 = EqProofBuilder::mk_congr_arg(CongrArgArgs {
            u: self.u.clone(),
            v: self.u.clone(),
            alpha: self.alpha.clone(),
            beta: self.alpha.clone(),
            f: make_add_left_lambda(&self.alpha, &next.lhs)?,
            a1: self.lhs.clone(),
            a2: self.rhs.clone(),
            h: self.proof,
        });
        let step2 = EqProofBuilder::mk_congr_arg(CongrArgArgs {
            u: self.u.clone(),
            v: self.u.clone(),
            alpha: self.alpha.clone(),
            beta: self.alpha.clone(),
            f: make_add_right_lambda(&self.alpha, &self.rhs)?,
            a1: next.lhs.clone(),
            a2: next.rhs.clone(),
            h: next.proof,
        });
        let lhs = make_add_app(&self.alpha, &self.lhs, &next.lhs)?;
        let middle = make_add_app(&self.alpha, &self.rhs, &next.lhs)?;
        let rhs = make_add_app(&self.alpha, &self.rhs, &next.rhs)?;
        let proof = EqProofBuilder::mk_eq_trans(
            self.u.clone(),
            self.alpha.clone(),
            lhs.clone(),
            middle,
            rhs.clone(),
            step1,
            step2,
        );
        Some(EqAcc {
            alpha: self.alpha,
            u: self.u,
            lhs,
            rhs,
            proof,
        })
    }
}

pub(super) fn get_sort_level(state: &ProofState, goal: &Goal, ty: &Expr) -> Option<Level> {
    let sort = state.infer_type(goal, ty).ok()?;
    match sort.kind() {
        ExprKind::Sort(level) => Some(level.clone()),
        _ => None,
    }
}

pub(super) fn prove_eq_by_ring_nf(
    state: &ProofState,
    goal: &Goal,
    eq_target: Expr,
) -> Option<Expr> {
    let mut scratch = state.clone_with_fresh_goal_target_in_context(eq_target, &goal.local_ctx);

    if ring_nf(&mut scratch).is_err() || !scratch.is_complete() {
        return None;
    }
    if scratch.trust_ledger().trusted_arith_count > 0 {
        return None;
    }
    scratch.proof_term()
}

pub(super) fn try_close_with_proof(
    state: &ProofState,
    goal: &Goal,
    proof: &Expr,
) -> Result<(), ()> {
    let proof_ty = state.infer_type(goal, proof).map_err(|_| ())?;
    let target = state.metas.instantiate(&goal.target);
    if state.is_def_eq(goal, &proof_ty, &target) {
        Ok(())
    } else {
        Err(())
    }
}

pub(super) fn cancel_shared_additive_witness(
    state: &ProofState,
    goal: &Goal,
    alpha: &Expr,
    goal_lhs: Expr,
    goal_rhs: Expr,
    witness: Expr,
    bridged_eq: Expr,
) -> Option<Expr> {
    let theorem = match carrier_name(alpha)? {
        "Nat" => Name::from_string("Nat.add_right_cancel"),
        "Int" => Name::from_string("Int.add_right_cancel"),
        "Rat" => Name::from_string("Rat.add_right_cancel"),
        "Real" => Name::from_string("Real.add_right_cancel"),
        _ => return None,
    };
    state.env().get_const(&theorem)?;
    let proof = Expr::apps(
        Expr::const_(theorem, vec![]),
        [goal_lhs, witness, goal_rhs, bridged_eq],
    );
    (try_close_with_proof(state, goal, &proof).is_ok()).then_some(proof)
}
