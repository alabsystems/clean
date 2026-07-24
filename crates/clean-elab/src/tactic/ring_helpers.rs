// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::ring_literals::nonnegative_ring_const_value;
use clean_kernel::name::Name;
use clean_kernel::{Expr, ExprKind, Level};

#[cfg(test)]
use clean_kernel::FVarId;

#[cfg(test)]
use super::tc_app;
#[cfg(test)]
use super::ProofState;
use crate::stack_safe;

/// Representation of a ring expression in normalized form
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum RingExpr {
    /// A constant (natural number for now)
    Const(u64),
    /// A variable (identified by name or fvar)
    Var(String),
    /// Addition of terms
    Add(Vec<RingExpr>),
    /// Multiplication of factors
    Mul(Vec<RingExpr>),
    /// Power (base, exponent)
    Pow(Box<RingExpr>, u64),
    /// Negation
    Neg(Box<RingExpr>),
    /// Unknown expression (treated as atomic)
    Unknown(String),
}

/// Try to match a binary ring operation from an application spine.
/// Checks operator name before normalizing args to avoid wasted computation
/// (e.g. @Neg.neg α inst a has nargs=3 but is unary, not binary).
///
/// REQUIRES: `op_str` is the string form of the constant head for the
/// application spine in `args`.
/// ENSURES: Returns `Some` only for recognized binary add/mul/sub/pow heads
/// with at least two explicit arguments.
/// ENSURES: `pow` returns `Some` only when the final argument normalizes to
/// `RingExpr::Const`; otherwise it returns `None`.
fn ring_match_binop(op_str: &str, args: &[&Expr]) -> Option<RingExpr> {
    let nargs = args.len();
    if nargs < 2 {
        return None;
    }
    let is_add = op_str.contains("add") || op_str.contains("Add");
    let is_mul = op_str.contains("mul") || op_str.contains("Mul");
    let is_sub = op_str.contains("sub") || op_str.contains("Sub");
    let is_pow = op_str.contains("pow") || op_str.contains("Pow");
    if !(is_add || is_mul || is_sub || is_pow) {
        return None;
    }
    let left = ring_normalize(args[nargs - 2]);
    let right = ring_normalize(args[nargs - 1]);
    if is_add {
        return Some(ring_flatten_add(left, right));
    }
    if is_mul {
        return Some(ring_flatten_mul(left, right));
    }
    if is_sub {
        return Some(ring_flatten_add(left, RingExpr::Neg(Box::new(right))));
    }
    if let RingExpr::Const(n) = right {
        return Some(ring_make_pow(left, n));
    }
    None
}

/// Build the canonical normal form for a power `base ^ exp` with a literal
/// natural exponent.
///
/// Folds the cases where the result is itself a canonical constant so that the
/// fast-path equality gate in `ring`/`ring_nf` recognizes them (mirroring
/// Lean 4's `ring`, which closes e.g. `(2 : Nat) ^ 3 = 8` and `a ^ 0 = 1`):
/// - `_ ^ 0` → `Const(1)` (universal ring identity; the kernel discharges the
///   resulting `rfl` goal via `Nat.pow _ 0` reduction).
/// - `Const(b) ^ n` → `Const(b^n)` when `b^n` fits in `u64` (the kernel's
///   `reduce_nat_pow` discharges the resulting `rfl` goal). Overflowing powers
///   stay symbolic so we never fabricate a wrong constant.
///
/// All other shapes keep the symbolic `Pow(base, exp)` form, exactly as before,
/// so this is purely a refinement that never reports two distinct values as
/// equal.
///
/// REQUIRES: `base` is an already-normalized ring fragment and `exp` is the
/// literal exponent.
/// ENSURES: The result is structurally equal to the normal form of the
/// expanded power whenever it collapses to a `Const`.
fn ring_make_pow(base: RingExpr, exp: u64) -> RingExpr {
    if exp == 0 {
        return RingExpr::Const(1);
    }
    if let RingExpr::Const(b) = base {
        if let Ok(e) = u32::try_from(exp) {
            if let Some(v) = b.checked_pow(e) {
                return RingExpr::Const(v);
            }
        }
        // Overflow: keep the (constant-base) power symbolic rather than wrap.
        return RingExpr::Pow(Box::new(RingExpr::Const(b)), exp);
    }
    RingExpr::Pow(Box::new(base), exp)
}

/// Try to match a unary ring operation (negation, successor).
///
/// REQUIRES: `op_str` is the string form of the constant head for the
/// application spine in `args`.
/// ENSURES: Returns `Some(Neg(_))` for negation heads and a normalized successor
/// encoding for `Nat.succ`; otherwise returns `None`.
fn ring_match_unop(op_str: &str, args: &[&Expr]) -> Option<RingExpr> {
    if args.is_empty() {
        return None;
    }
    let last = args[args.len() - 1];
    if op_str.contains("neg") || op_str.contains("Neg") {
        return Some(RingExpr::Neg(Box::new(ring_normalize(last))));
    }
    if op_str == "Nat.succ" {
        let operand = ring_normalize(last);
        if let RingExpr::Const(n) = operand {
            return Some(RingExpr::Const(n + 1));
        }
        return Some(ring_flatten_add(operand, RingExpr::Const(1)));
    }
    None
}

/// Normalize a ring expression
///
/// REQUIRES: `expr` is a well-formed expression tree.
/// ENSURES: Recognized arithmetic application spines normalize into flattened
/// `RingExpr` structure with Nat literals mapped to `Const`.
/// ENSURES: Unrecognized heads and unsupported literals become atomic
/// `Var`/`Unknown` nodes instead of panicking.
/// ENSURES: Recursive descent runs under `stack_safe`.
pub(crate) fn ring_normalize(expr: &Expr) -> RingExpr {
    stack_safe(|| {
        if let Some(value) = nonnegative_ring_const_value(expr) {
            return RingExpr::Const(value);
        }

        match expr.kind() {
            ExprKind::Const(name, _) => {
                let s = name.to_string();
                RingExpr::Var(s)
            }
            ExprKind::FVar(id) => RingExpr::Var(format!("fvar_{}", id.as_u64())),
            ExprKind::App(_, _) => {
                let head = expr.get_app_fn();
                if let ExprKind::Const(op_name, _) = head.kind() {
                    let op_str = op_name.to_string();
                    let args = expr.get_app_args();
                    if let Some(r) = ring_match_binop(&op_str, &args) {
                        return r;
                    }
                    if let Some(r) = ring_match_unop(&op_str, &args) {
                        return r;
                    }
                }
                RingExpr::Unknown(format!("{expr:?}"))
            }
            _ => RingExpr::Unknown(format!("{expr:?}")),
        }
    })
}

/// Flatten addition: a + (b + c) → Add([a, b, c])
///
/// REQUIRES: `left` and `right` are already normalized ring fragments.
/// ENSURES: Result has no nested top-level `Add`; constant and duplicate terms
/// are simplified through `ring_collect_like_terms`.
/// ENSURES: Returns `Const(0)` for an empty sum and the lone term for a
/// singleton sum.
pub(crate) fn ring_flatten_add(left: RingExpr, right: RingExpr) -> RingExpr {
    let mut terms = Vec::new();

    match left {
        RingExpr::Add(ts) => terms.extend(ts),
        other => terms.push(other),
    }

    match right {
        RingExpr::Add(ts) => terms.extend(ts),
        other => terms.push(other),
    }

    terms = ring_collect_like_terms(terms);

    match terms.len() {
        0 => RingExpr::Const(0),
        1 => terms.pop().expect("terms has exactly 1 element"),
        _ => {
            terms.sort();
            RingExpr::Add(terms)
        }
    }
}

/// Flatten multiplication: a * (b * c) → Mul([a, b, c])
///
/// REQUIRES: `left` and `right` are already normalized ring fragments.
/// ENSURES: Result has no nested top-level `Mul`; constant factors are
/// collapsed into at most one leading `Const`.
/// ENSURES: Returns `Const(0)` if any factor is zero and omits multiplicative
/// identity `1` unless it is the only remaining factor.
pub(crate) fn ring_flatten_mul(left: RingExpr, right: RingExpr) -> RingExpr {
    let mut factors = Vec::new();

    match left {
        RingExpr::Mul(fs) => factors.extend(fs),
        other => factors.push(other),
    }

    match right {
        RingExpr::Mul(fs) => factors.extend(fs),
        other => factors.push(other),
    }

    // Distribute over addition: a * (b + c) * d → (a*b*d) + (a*c*d).
    // Take the first Add factor, distribute, then recurse (handles nested Adds).
    if let Some(add_idx) = factors.iter().position(|f| matches!(f, RingExpr::Add(_))) {
        let add_factor = factors.remove(add_idx);
        if let RingExpr::Add(addends) = add_factor {
            let distributed: Vec<RingExpr> = addends
                .into_iter()
                .map(|t| {
                    let mut term_factors = factors.clone();
                    term_factors.push(t);
                    ring_mul_factors(term_factors)
                })
                .collect();
            return ring_add_terms(distributed);
        }
    }

    let (consts, vars): (Vec<_>, Vec<_>) = factors
        .into_iter()
        .partition(|f| matches!(f, RingExpr::Const(_)));

    let const_product: u64 = consts
        .iter()
        .filter_map(|c| {
            if let RingExpr::Const(n) = c {
                Some(*n)
            } else {
                None
            }
        })
        .product();

    if const_product == 0 {
        return RingExpr::Const(0);
    }

    let mut result = vars;
    if const_product != 1 {
        result.insert(0, RingExpr::Const(const_product));
    }

    match result.len() {
        0 => RingExpr::Const(1),
        1 => result.pop().expect("result has exactly 1 element"),
        _ => {
            result.sort();
            RingExpr::Mul(result)
        }
    }
}

/// Multiply a list of factors, distributing over any Add factors.
fn ring_mul_factors(factors: Vec<RingExpr>) -> RingExpr {
    factors
        .into_iter()
        .reduce(ring_flatten_mul)
        .unwrap_or(RingExpr::Const(1))
}

/// Flatten a list of addends through `ring_flatten_add`.
fn ring_add_terms(terms: Vec<RingExpr>) -> RingExpr {
    terms
        .into_iter()
        .reduce(ring_flatten_add)
        .unwrap_or(RingExpr::Const(0))
}

/// Split a monomial addend into its integer coefficient and its sorted
/// variable-factor multiset.
///
/// This is the canonicalization key for like-term merging (#ring-coeff-merge):
/// two addends are "like" iff their variable-factor multisets are equal,
/// regardless of the numeric coefficient. Examples:
/// - `a*b`                  → (1,  [a, b])
/// - `Mul([Const(2), a, b])`→ (2,  [a, b])
/// - `-(a*b)`               → (-1, [a, b])
/// - `Const(3)`             → (3,  [])
/// - `a`                    → (1,  [a])
///
/// REQUIRES: `term` is a normalized addend (already flattened by
/// `ring_flatten_mul` so any `Mul` has at most one leading `Const`).
/// ENSURES: The returned variable list is sorted (matching the canonical
/// `RingExpr::Mul` factor order), so equal monomials produce equal keys.
fn monomial_key(term: &RingExpr) -> (i64, Vec<RingExpr>) {
    match term {
        RingExpr::Const(n) => (*n as i64, Vec::new()),
        RingExpr::Neg(inner) => {
            let (coeff, vars) = monomial_key(inner);
            (-coeff, vars)
        }
        RingExpr::Mul(factors) => {
            let mut coeff: i64 = 1;
            let mut vars: Vec<RingExpr> = Vec::new();
            for f in factors {
                match f {
                    RingExpr::Const(n) => coeff *= *n as i64,
                    other => vars.push(other.clone()),
                }
            }
            vars.sort();
            (coeff, vars)
        }
        // Atom (Var / Pow / Unknown): coefficient 1, single-factor multiset.
        other => (1, vec![other.clone()]),
    }
}

/// Rebuild a single addend from a (coefficient, sorted-variable-multiset) pair.
///
/// Mirrors the canonical `Mul`/`Const`/`Neg` shapes produced elsewhere in the
/// normalizer so the result is comparable by structural equality:
/// - `c == 0`                  → `Const(0)` (caller drops these)
/// - `c < 0`                   → `Neg(positive form)`
/// - `c == 1`, vars `[v]`      → `v`
/// - `c == 1`, vars `[v0, v1]` → `Mul([v0, v1, ...])`
/// - `c != 1`                  → `Mul([Const(c), ...vars])`
///
/// REQUIRES: `vars` is already sorted.
/// ENSURES: The returned addend has the canonical coefficient layout
/// (`Const` first inside any `Mul`).
fn rebuild_monomial(coeff: i64, vars: &[RingExpr]) -> RingExpr {
    if coeff < 0 {
        return RingExpr::Neg(Box::new(rebuild_monomial(-coeff, vars)));
    }
    // coeff >= 0 below.
    let c = coeff as u64;
    if vars.is_empty() {
        return RingExpr::Const(c);
    }
    if c == 1 {
        if vars.len() == 1 {
            return vars[0].clone();
        }
        return RingExpr::Mul(vars.to_vec());
    }
    if c == 0 {
        return RingExpr::Const(0);
    }
    let mut factors = Vec::with_capacity(vars.len() + 1);
    factors.push(RingExpr::Const(c));
    factors.extend(vars.iter().cloned());
    RingExpr::Mul(factors)
}

/// Collect like terms in an addition, merging like monomials into a single
/// constant-coefficient form.
///
/// Like monomials (same sorted variable-factor multiset) are fused by SUMMING
/// their integer coefficients: `a*b + a*b` becomes `Mul([Const(2), a, b])`
/// (not two repeated `a*b` addends), and `Mul([Const(2),a,b]) + a*b` becomes
/// `Mul([Const(3),a,b])`. This is the canonical Horner-style coefficient
/// merge: the syntactic normal form now agrees with the proof-carrying
/// normalizer's fused output (#ring-coeff-merge), so `(a+b)*(a+b)` and
/// `a*a + 2*a*b + b*b` reduce to the same `RingExpr`.
///
/// REQUIRES: `terms` are normalized addends (each already flattened by
/// `ring_flatten_mul`).
/// ENSURES: All bare constant contributions are aggregated into at most one
/// constant term.
/// ENSURES: Each distinct variable-factor multiset appears at most once, with
/// its net signed coefficient; zero-coefficient monomials are removed.
pub(crate) fn ring_collect_like_terms(terms: Vec<RingExpr>) -> Vec<RingExpr> {
    use std::collections::HashMap;

    let mut const_sum: i64 = 0;
    // Key: sorted variable-factor multiset. Value: summed integer coefficient.
    let mut mono_coeffs: HashMap<Vec<RingExpr>, i64> = HashMap::new();
    // Preserve first-seen order of distinct monomials for deterministic output
    // (the caller sorts afterward, but determinism aids debugging).
    let mut order: Vec<Vec<RingExpr>> = Vec::new();

    for term in terms {
        let (coeff, vars) = monomial_key(&term);
        if vars.is_empty() {
            const_sum += coeff;
            continue;
        }
        let entry = mono_coeffs.entry(vars.clone());
        if matches!(entry, std::collections::hash_map::Entry::Vacant(_)) {
            order.push(vars.clone());
        }
        *entry.or_insert(0) += coeff;
    }

    let mut result = Vec::new();

    if const_sum > 0 {
        result.push(RingExpr::Const(const_sum as u64));
    } else if const_sum < 0 {
        result.push(RingExpr::Neg(Box::new(RingExpr::Const(
            (-const_sum) as u64,
        ))));
    }

    for vars in &order {
        let coeff = mono_coeffs.get(vars).copied().unwrap_or(0);
        if coeff != 0 {
            result.push(rebuild_monomial(coeff, vars));
        }
    }

    result
}

/// Check if two normalized ring expressions are equal
///
/// ENSURES: Returns `true` iff `a` and `b` are structurally equal canonical
/// `RingExpr` values.
pub(crate) fn ring_exprs_equal(a: &RingExpr, b: &RingExpr) -> bool {
    a == b
}

/// Convert RingExpr back to Expr
///
/// REQUIRES: Symbolic names inside `re` are valid constants or encoded
/// `fvar_<id>` locals for downstream typing.
/// ENSURES: Reconstructs an expression whose recursive application structure
/// matches `re`.
/// ENSURES: `Var("fvar_N")` round-trips to `Expr::fvar(FVarId::new(N))`;
/// other symbolic leaves become constants.
#[cfg(test)]
pub(crate) fn ring_expr_to_expr(re: &RingExpr, state: &mut ProofState) -> Expr {
    match re {
        RingExpr::Const(n) => Expr::nat_lit(*n),
        RingExpr::Var(s) => {
            if let Some(suffix) = s.strip_prefix("fvar_") {
                if let Ok(id) = suffix.parse::<u64>() {
                    return Expr::fvar(FVarId::new(id));
                }
            }
            state.mk_const_str(s)
        }
        RingExpr::Add(terms) => {
            if terms.is_empty() {
                return Expr::nat_lit(0);
            }
            let mut result = ring_expr_to_expr(&terms[0], state);
            for term in &terms[1..] {
                let term_expr = ring_expr_to_expr(term, state);
                result = make_add(&result, &term_expr, state);
            }
            result
        }
        RingExpr::Mul(factors) => {
            if factors.is_empty() {
                return Expr::nat_lit(1);
            }
            let mut result = ring_expr_to_expr(&factors[0], state);
            for factor in &factors[1..] {
                let factor_expr = ring_expr_to_expr(factor, state);
                result = make_mul(&result, &factor_expr, state);
            }
            result
        }
        RingExpr::Pow(base, exp) => {
            let base_expr = ring_expr_to_expr(base, state);
            let exp_expr = Expr::nat_lit(*exp);
            make_pow(&base_expr, &exp_expr, state)
        }
        RingExpr::Neg(inner) => {
            let inner_expr = ring_expr_to_expr(inner, state);
            make_neg(&inner_expr, state)
        }
        RingExpr::Unknown(s) => state.mk_const_str(s),
    }
}

/// Make addition expression: `@HAdd.hAdd.{u,v,w} α β γ inst a b`
///
/// For the common homogeneous case (α = β = γ = Nat), uses `instHAddNat`.
/// Part of #2078: previously only produced `HAdd.hAdd a b` (missing 4 implicit args).
///
/// REQUIRES: `a` and `b` are expressions intended for the Nat `HAdd` instance
/// hard-coded by `ring_nf`.
/// ENSURES: Returns a fully-applied `HAdd.hAdd` expression with Nat type and
/// instance arguments filled in.
#[cfg(test)]
pub(crate) fn make_add(a: &Expr, b: &Expr, _state: &mut ProofState) -> Expr {
    let ty = tc_app::nat_type();
    let inst = tc_app::nat_arith_inst("HAdd.hAdd");
    tc_app::mk_tc_hbinop(
        Expr::const_(
            Name::from_string("HAdd.hAdd"),
            vec![Level::zero(), Level::zero(), Level::zero()],
        ),
        ty.clone(),
        ty.clone(),
        ty,
        inst,
        a.clone(),
        b.clone(),
    )
}

/// Make multiplication expression: `@HMul.hMul.{u,v,w} α β γ inst a b`
///
/// Part of #2078: previously only produced `HMul.hMul a b` (missing 4 implicit args).
///
/// REQUIRES: `a` and `b` are expressions intended for the Nat `HMul` instance
/// hard-coded by `ring_nf`.
/// ENSURES: Returns a fully-applied `HMul.hMul` expression with Nat type and
/// instance arguments filled in.
#[cfg(test)]
pub(crate) fn make_mul(a: &Expr, b: &Expr, _state: &mut ProofState) -> Expr {
    let ty = tc_app::nat_type();
    let inst = tc_app::nat_arith_inst("HMul.hMul");
    tc_app::mk_tc_hbinop(
        Expr::const_(
            Name::from_string("HMul.hMul"),
            vec![Level::zero(), Level::zero(), Level::zero()],
        ),
        ty.clone(),
        ty.clone(),
        ty,
        inst,
        a.clone(),
        b.clone(),
    )
}

/// Make power expression: `@HPow.hPow.{u,v,w} α β γ inst base exp`
///
/// Part of #2078: previously only produced `HPow.hPow base exp` (missing 4 implicit args).
///
/// REQUIRES: `base` and `exp` are expressions intended for the Nat `HPow`
/// instance hard-coded by `ring_nf`.
/// ENSURES: Returns a fully-applied `HPow.hPow` expression with Nat type and
/// instance arguments filled in.
#[cfg(test)]
pub(crate) fn make_pow(base: &Expr, exp: &Expr, _state: &mut ProofState) -> Expr {
    let ty = tc_app::nat_type();
    let inst = tc_app::nat_arith_inst("HPow.hPow");
    tc_app::mk_tc_hbinop(
        Expr::const_(
            Name::from_string("HPow.hPow"),
            vec![Level::zero(), Level::zero(), Level::zero()],
        ),
        ty.clone(),
        ty.clone(),
        ty,
        inst,
        base.clone(),
        exp.clone(),
    )
}

/// Make negation expression: `@Neg.neg.{u} α inst a`
///
/// Part of #2078: previously only produced `Neg.neg a` (missing type + instance).
///
/// REQUIRES: `a` is an expression intended for the Int `Neg` instance
/// hard-coded by `ring_nf`.
/// ENSURES: Returns a fully-applied `Neg.neg` expression with Int type and
/// instance arguments filled in.
#[cfg(test)]
pub(crate) fn make_neg(a: &Expr, _state: &mut ProofState) -> Expr {
    let ty = Expr::const_(Name::from_string("Int"), vec![]);
    let inst = tc_app::nat_arith_inst("Neg.neg");
    tc_app::mk_tc_unop(
        Expr::const_(Name::from_string("Neg.neg"), vec![Level::zero()]),
        ty,
        inst,
        a.clone(),
    )
}

/// Make equality expression
///
/// REQUIRES: `ty`, `lhs`, and `rhs` are well-formed and `lhs`/`rhs` inhabit
/// `ty`.
/// ENSURES: Returns the fully-applied `Eq ty lhs rhs` expression using
/// `levels` for the `Eq` constant.
pub(crate) fn make_eq(ty: &Expr, lhs: &Expr, rhs: &Expr, levels: &[Level]) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), levels.to_vec()),
                ty.clone(),
            ),
            lhs.clone(),
        ),
        rhs.clone(),
    )
}
