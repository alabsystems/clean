// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Bridge-local Int additive normal form for symbolic closeout (#302).
//
// Flattens `Int.add` trees into additive leaves, transports the accumulator
// proof onto a grouped `(prefix + shared)` shape, and then cancels the common
// shared suffix with the kernel `Int.*_of_add_*_add_right` lemmas.

use clean_kernel::name::Name;
use clean_kernel::{BigNat, BinderInfo, Expr, ExprKind, Level, Literal};
use num_bigint::BigInt;
#[cfg(test)]
use num_bigint::Sign;

use super::expr_builders;
use super::expr_builders_arith::{self, CmpOp};
use super::theory_lemma_lra_additive::mk_int_add;

mod identical_suffix;
#[cfg(test)]
mod identical_suffix_tests;
#[cfg(test)]
mod tests;
mod transport;
#[cfg(test)]
mod transport_stack_safe_tests;

use transport::{build_right_assoc_expr, normalize_cmp_proof};

/// Additive normal form for Int expressions.
///
/// Decomposes an Int expression into:
/// - `atoms`: opaque non-additive subexpressions (symbolic)
/// - `constant_terms`: the concrete literal addends in encounter order
/// - `constant`: accumulated concrete `Int.ofNat` / `Int.negSucc` sum
///
/// This is intentionally NOT a polynomial reifier. The bridge only
/// needs additive atom cancellation.
#[derive(Debug, Clone)]
pub(super) struct IntAddNf {
    pub(super) atoms: Vec<Expr>,
    pub(super) constant_terms: Vec<Expr>,
    pub(super) constant: BigInt,
}

impl IntAddNf {
    /// Flatten an Int expression into additive normal form.
    pub(super) fn from_expr(expr: &Expr) -> Self {
        let mut nf = IntAddNf {
            atoms: Vec::new(),
            constant_terms: Vec::new(),
            constant: BigInt::from(0),
        };
        nf.flatten(expr);
        nf
    }

    fn flatten(&mut self, expr: &Expr) {
        crate::bridge::stack_safe(|| {
            let expr = expr.strip_mdata();
            if let Some((a, b)) = Self::as_flatten_add(expr) {
                self.flatten(a);
                self.flatten(b);
                return;
            }

            if let Some(v) = extract_int_literal(expr) {
                self.constant += &v;
                self.constant_terms.push(expr.clone());
                return;
            }

            self.atoms.push(expr.clone());
        })
    }

    fn as_flatten_add(expr: &Expr) -> Option<(&Expr, &Expr)> {
        let expr = expr.strip_mdata();
        let args = expr.get_app_args();
        if args.len() < 2 {
            return None;
        }

        if let ExprKind::Const(name, _) = expr.get_app_fn().strip_mdata().kind() {
            match name.to_string().as_str() {
                "Int.add" | "Add.add" | "HAdd.hAdd" => {
                    let arity = args.len();
                    return Some((args[arity - 2], args[arity - 1]));
                }
                _ => {}
            }
        }
        None
    }

    fn as_raw_int_add(expr: &Expr) -> Option<(&Expr, &Expr)> {
        let expr = expr.strip_mdata();
        let args = expr.get_app_args();
        if args.len() < 2 {
            return None;
        }
        if let ExprKind::Const(name, _) = expr.get_app_fn().strip_mdata().kind() {
            if name.to_string() == "Int.add" {
                let arity = args.len();
                return Some((args[arity - 2], args[arity - 1]));
            }
        }
        None
    }

    fn as_alias_int_add(expr: &Expr) -> Option<(&Expr, &Expr)> {
        let expr = expr.strip_mdata();
        let args = expr.get_app_args();
        if args.len() < 2 {
            return None;
        }
        if let ExprKind::Const(name, _) = expr.get_app_fn().strip_mdata().kind() {
            match name.to_string().as_str() {
                "Add.add" | "HAdd.hAdd" => {
                    let arity = args.len();
                    Some((args[arity - 2], args[arity - 1]))
                }
                _ => None,
            }
        } else {
            None
        }
    }

    /// Reconstruct a normalized Int expression from the aggregated normal form.
    ///
    /// This is used by the local unit tests. The proof transport path keeps the
    /// original concrete literal terms separate so it only needs assoc/comm.
    #[cfg(test)]
    pub(super) fn to_expr(&self) -> Expr {
        let const_expr = mk_bigint_literal(&self.constant);
        if self.atoms.is_empty() {
            return const_expr;
        }
        let mut result = self
            .atoms
            .last()
            .expect("invariant: atoms non-empty")
            .clone();
        for atom in self.atoms.iter().rev().skip(1) {
            result = mk_int_add(atom, &result);
        }
        mk_int_add(&const_expr, &result)
    }
}

/// Close shape for cancellation: partitions two normal forms into
/// lhs-only, rhs-only, and shared atoms.
///
/// The concrete literal heads are kept in encounter order so the proof
/// transport only needs assoc/comm plus optional `Int.zero_add`.
#[derive(Debug, Clone)]
pub(super) struct IntCloseShape {
    pub(super) lhs_only: Vec<Expr>,
    pub(super) rhs_only: Vec<Expr>,
    pub(super) shared: Vec<Expr>,
    pub(super) lhs_const_terms: Vec<Expr>,
    pub(super) rhs_const_terms: Vec<Expr>,
    pub(super) lhs_const: BigInt,
    pub(super) rhs_const: BigInt,
}

impl IntCloseShape {
    /// Check if the residual (after cancellation) is concrete and contradictory.
    pub(super) fn residual_is_concrete_contradiction(&self, op: CmpOp) -> bool {
        if !self.lhs_only.is_empty() || !self.rhs_only.is_empty() {
            return false;
        }
        match op {
            CmpOp::Le => self.lhs_const > self.rhs_const,
            CmpOp::Lt => self.lhs_const >= self.rhs_const,
        }
    }

    fn build_prefix_terms(&self, constant_terms: &[Expr], only: &[Expr]) -> Vec<Expr> {
        constant_terms
            .iter()
            .cloned()
            .chain(only.iter().cloned())
            .collect()
    }

    fn lhs_prefix_terms(&self) -> Vec<Expr> {
        self.build_prefix_terms(&self.lhs_const_terms, &self.lhs_only)
    }

    fn rhs_prefix_terms(&self) -> Vec<Expr> {
        self.build_prefix_terms(&self.rhs_const_terms, &self.rhs_only)
    }

    fn shared_expr(&self) -> Option<Expr> {
        if self.shared.is_empty() {
            None
        } else {
            Some(build_right_assoc_expr(&self.shared))
        }
    }

    pub(super) fn lhs_prefix_expr(&self) -> Expr {
        let terms = self.lhs_prefix_terms();
        if terms.is_empty() {
            mk_int_literal(0)
        } else {
            build_right_assoc_expr(&terms)
        }
    }

    pub(super) fn rhs_prefix_expr(&self) -> Expr {
        let terms = self.rhs_prefix_terms();
        if terms.is_empty() {
            mk_int_literal(0)
        } else {
            build_right_assoc_expr(&terms)
        }
    }

    /// Build the lhs expression for the close shape.
    pub(super) fn lhs_expr(&self) -> Expr {
        self.build_side_expr(self.lhs_prefix_expr())
    }

    /// Build the rhs expression for the close shape.
    pub(super) fn rhs_expr(&self) -> Expr {
        self.build_side_expr(self.rhs_prefix_expr())
    }

    fn build_side_expr(&self, prefix: Expr) -> Expr {
        match self.shared_expr() {
            Some(shared) => mk_int_add(&prefix, &shared),
            None => prefix,
        }
    }
}

/// Partition two IntAddNf into a close shape by multiset-matching atoms.
pub(super) fn build_close_shape(lhs: &IntAddNf, rhs: &IntAddNf) -> IntCloseShape {
    let mut rhs_remaining: Vec<Option<Expr>> = rhs.atoms.iter().map(|a| Some(a.clone())).collect();
    let mut lhs_only = Vec::new();
    let mut shared = Vec::new();

    for lhs_atom in &lhs.atoms {
        let mut matched = false;
        for slot in rhs_remaining.iter_mut() {
            if let Some(rhs_atom) = slot {
                if exprs_syntactically_equal(lhs_atom, rhs_atom) {
                    shared.push(lhs_atom.clone());
                    *slot = None;
                    matched = true;
                    break;
                }
            }
        }
        if !matched {
            lhs_only.push(lhs_atom.clone());
        }
    }

    let rhs_only: Vec<Expr> = rhs_remaining.into_iter().flatten().collect();

    IntCloseShape {
        lhs_only,
        rhs_only,
        shared,
        lhs_const_terms: lhs.constant_terms.clone(),
        rhs_const_terms: rhs.constant_terms.clone(),
        lhs_const: lhs.constant.clone(),
        rhs_const: rhs.constant.clone(),
    }
}

/// Build Int cancellation lemma application.
///
/// Given `h : (a + c) op (b + c)`, produce
/// `Int.le_of_add_le_add_right a c b h` (or the strict variant) to get
/// `a op b`.
pub(super) fn mk_int_cancel_add_right(
    op: CmpOp,
    a: &Expr,
    shared: &Expr,
    b: &Expr,
    h: &Expr,
) -> Expr {
    let name = match op {
        CmpOp::Le => "Int.le_of_add_le_add_right",
        CmpOp::Lt => "Int.lt_of_add_lt_add_right",
    };
    mk_4arg(name, a, shared, b, h)
}

/// Attempt to close a symbolic additive contradiction via normal-form
/// cancellation.
///
/// Given an accumulator proof of `acc_lhs op acc_rhs` where both sides
/// are Int.add trees, normalize both to IntAddNf, compute the close
/// shape, cancel the shared suffix, and close the residual concrete
/// contradiction.
///
/// Returns `Some(false_proof)` on success, `None` if the residual is
/// not a concrete contradiction (fail closed).
pub(super) fn try_close_int_additive_nf(
    op: CmpOp,
    acc_lhs: &Expr,
    acc_rhs: &Expr,
    acc_proof: &Expr,
) -> Option<Expr> {
    if let Some(false_proof) =
        identical_suffix::try_close_identical_raw_add_suffix(op, acc_lhs, acc_rhs, acc_proof)
    {
        return Some(false_proof);
    }

    let lhs_nf = IntAddNf::from_expr(acc_lhs);
    let rhs_nf = IntAddNf::from_expr(acc_rhs);
    let shape = build_close_shape(&lhs_nf, &rhs_nf);

    if !shape.residual_is_concrete_contradiction(op) {
        return None;
    }

    let normalized = normalize_cmp_proof(op, acc_lhs, acc_rhs, &shape, acc_proof)?;
    let residual_proof = match shape.shared_expr() {
        Some(shared) => mk_int_cancel_add_right(
            op,
            &shape.lhs_prefix_expr(),
            &shared,
            &shape.rhs_prefix_expr(),
            &normalized,
        ),
        None => normalized,
    };

    Some(expr_builders_arith::mk_int_concrete_false(
        op,
        &shape.lhs_prefix_expr(),
        &shape.rhs_prefix_expr(),
        &residual_proof,
    ))
}

fn mk_4arg(name: &str, a: &Expr, b: &Expr, c: &Expr, d: &Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::const_(Name::from_string(name), vec![]), a.clone()),
                b.clone(),
            ),
            c.clone(),
        ),
        d.clone(),
    )
}

fn mk_int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

fn mk_int_to_int_type() -> Expr {
    Expr::pi(BinderInfo::Default, mk_int_ty(), mk_int_ty())
}

fn mk_int_to_prop_type() -> Expr {
    Expr::pi(BinderInfo::Default, mk_int_ty(), Expr::sort(Level::zero()))
}

fn mk_cmp_prop(op: CmpOp, lhs: &Expr, rhs: &Expr) -> Expr {
    let name = match op {
        CmpOp::Le => "Int.le",
        CmpOp::Lt => "Int.lt",
    };
    Expr::app(
        Expr::app(Expr::const_(Name::from_string(name), vec![]), lhs.clone()),
        rhs.clone(),
    )
}

fn mk_int_eq_refl(val: &Expr) -> Expr {
    expr_builders::mk_eq_refl(&mk_int_ty(), val)
}

fn mk_int_eq_symm(a: &Expr, b: &Expr, h: &Expr) -> Expr {
    expr_builders::mk_eq_symm(&mk_int_ty(), a, b, h)
}

fn mk_int_eq_trans(a: &Expr, b: &Expr, c: &Expr, h1: &Expr, h2: &Expr) -> Expr {
    expr_builders::mk_eq_trans(&mk_int_ty(), a, b, c, h1, h2)
}

/// Build a concrete Int literal expression for small synthetic values.
fn mk_int_literal(value: i64) -> Expr {
    if value >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            Expr::nat_lit(value as u64),
        )
    } else {
        let n = (-value - 1) as u64;
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            Expr::nat_lit(n),
        )
    }
}

#[cfg(test)]
fn mk_bigint_literal(value: &BigInt) -> Expr {
    let nat_lit = |n: &BigInt| -> Expr {
        let (_, limbs) = n.to_u64_digits();
        Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::from_limbs(limbs))))
    };

    match value.sign() {
        Sign::Minus => {
            let neg_succ = -value - BigInt::from(1);
            Expr::app(
                Expr::const_(Name::from_string("Int.negSucc"), vec![]),
                nat_lit(&neg_succ),
            )
        }
        Sign::NoSign | Sign::Plus => Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat_lit(value),
        ),
    }
}

/// Evaluate a Nat expression in either literal or constructor form to a `BigInt`.
///
/// Recognizes:
/// - `Literal::Nat(n)` — kernel literal form
/// - `Nat.zero` — constructor zero
/// - `Nat.succ(n)` — constructor successor (recursive)
pub(super) fn eval_nat_to_bigint(expr: &Expr) -> Option<BigInt> {
    fn nat_bigint(n: &BigNat) -> BigInt {
        let mut acc = BigInt::from(0);
        for limb in n.limbs().iter().rev() {
            acc = (acc << 64) + BigInt::from(*limb);
        }
        acc
    }

    crate::bridge::stack_safe(|| {
        let expr = expr.strip_mdata();
        match expr.kind() {
            ExprKind::Lit(Literal::Nat(n)) => Some(nat_bigint(n)),
            ExprKind::Const(name, _) if name.to_string() == "Nat.zero" => Some(BigInt::from(0)),
            ExprKind::App(f, arg) => {
                if let ExprKind::Const(name, _) = f.strip_mdata().kind() {
                    if name.to_string() == "Nat.succ" {
                        return eval_nat_to_bigint(arg).map(|n| n + BigInt::from(1));
                    }
                }
                None
            }
            _ => None,
        }
    })
}

/// Extract a concrete Int literal from `Int.ofNat n` / `Int.negSucc n`.
///
/// The Nat argument `n` may be either a kernel `Literal::Nat` or a
/// constructor-form expression (`Nat.zero`, `Nat.succ`).
fn extract_int_literal(expr: &Expr) -> Option<BigInt> {
    let expr = expr.strip_mdata();
    if let ExprKind::App(f, arg) = expr.kind() {
        if let ExprKind::Const(name, _) = f.strip_mdata().kind() {
            let s = name.to_string();
            if let Some(n) = eval_nat_to_bigint(arg) {
                if s == "Int.ofNat" {
                    return Some(n);
                }
                if s == "Int.negSucc" {
                    return Some(-(n + BigInt::from(1)));
                }
            }
        }
    }
    None
}

/// Syntactic equality check for Expr (structural, no normalization).
fn exprs_syntactically_equal(a: &Expr, b: &Expr) -> bool {
    a == b
}

fn is_zero_literal(expr: &Expr) -> bool {
    extract_int_literal(expr).is_some_and(|value| value == BigInt::from(0))
}
