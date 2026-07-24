// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native `Nat` literal reduction + structural `Nat` (succ/zero) offset equality
//! for the certificate subsystem (both `CertBuilder` and `CertVerifier`).
//!
//! ## Why this module exists (the cert-replay Nat-defeq gap)
//!
//! The cert subsystem keeps its OWN minimal WHNF / def_eq (`cert/reduction.rs`,
//! `cert/builder/reduction.rs`, `cert/expr_eq.rs`) — separate from the main
//! `tc` type checker, by design: the verifier is the *independent re-checker* of
//! a `.cleancert` bundle. That minimal path implemented beta / zeta / delta /
//! iota / quotient / projection but NOT the `Nat`-literal reductions and
//! successor/zero peeling the main kernel (`tc/reduction/nat.rs`,
//! `tc/def_eq/delta.rs`) performs. Consequence: a genuine `Nat`-counting proof
//! that `clean check` ACCEPTS (the main path reduces `Nat.succ 3 ≡ 4`,
//! `Nat.add 2 3 ≡ 5`, `Nat.ble 3 5 ≡ true`) FAILED `clean export-cert` replay,
//! e.g. `Nat.le 3 4` vs `Nat.le 3 (Nat.succ 3)` reported a `Type mismatch at
//! App argument`. That blocked rhs=k cardinality-encoder faithfulness, whose
//! natural statement counts with `Nat`.
//!
//! ## What it adds (Lean 4 parity, no soundness widening)
//!
//! * [`reduce_nat`]        — closed `Nat` arithmetic to a literal: `Nat.succ`,
//!   `Nat.add/sub/mul/div/mod/gcd/pow`, `Nat.beq/ble`, and the bitwise/shift
//!   ops. Mirrors `tc/reduction/nat.rs::reduce_nat` (Lean 4
//!   `type_checker.cpp::reduce_nat`).
//! * [`is_def_eq_offset`]  — `0 ≟ 0` and `succ a ≟ succ b → a ≟ b` peeling on
//!   the WHNF'd sides, handling the mixed literal/`Nat.succ` and OPEN-successor
//!   forms a closed-only `reduce_nat` cannot evaluate. Mirrors
//!   `tc/reduction/nat.rs::is_def_eq_offset` (Lean 4 `is_def_eq_offset`).
//!
//! These are reductions/equalities already performed by `clean check` and by
//! Lean 4's kernel; they are valid CIC definitional equalities (literal
//! arithmetic is the value the term computes to; successor peeling is
//! constructor injectivity + the zero base case). This module therefore only
//! stops the verifier from REJECTING valid `Nat` proofs — it never makes it
//! accept a false one. The `*_REJECTED` controls (which the kernel must still
//! reject) confirm the boundary is intact.

use crate::expr::{BigNat, Expr, ExprKind, Literal};

/// Well-known `Nat`/`Bool` names used by the cert-side reducer. Cached as
/// statics to avoid re-allocating `Name`s on every WHNF step (same pattern as
/// `tc/reduction/mod.rs::names` and `crate::quot::names`).
pub(super) mod names {
    use crate::name::Name;
    use std::sync::LazyLock;

    pub static NAT_ZERO: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.zero"));
    pub static NAT_SUCC: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.succ"));
    pub static NAT_ADD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.add"));
    pub static NAT_SUB: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.sub"));
    pub static NAT_MUL: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.mul"));
    pub static NAT_DIV: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.div"));
    pub static NAT_MOD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.mod"));
    pub static NAT_GCD: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.gcd"));
    pub static NAT_POW: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.pow"));
    pub static NAT_BEQ: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.beq"));
    pub static NAT_BLE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.ble"));
    pub static NAT_LAND: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.land"));
    pub static NAT_LOR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.lor"));
    pub static NAT_XOR: LazyLock<Name> = LazyLock::new(|| Name::from_string("Nat.xor"));
    pub static NAT_SHIFT_LEFT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Nat.shiftLeft"));
    pub static NAT_SHIFT_RIGHT: LazyLock<Name> =
        LazyLock::new(|| Name::from_string("Nat.shiftRight"));
    pub static BOOL_TRUE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.true"));
    pub static BOOL_FALSE: LazyLock<Name> = LazyLock::new(|| Name::from_string("Bool.false"));
}

/// Convert a `Nat` literal to constructor form (lazily): `0 ↦ Nat.zero`,
/// `n+1 ↦ Nat.succ (Nat.lit n)`. Mirrors `tc/reduction/nat.rs::nat_lit_to_constructor`
/// (Lean 4 `nat_lit_to_constructor`). Lets `Nat.rec`/`Nat.ble`/`Nat.pred`/… iota-reduce
/// on a literal major premise inside the cert verifier.
pub(super) fn nat_lit_to_constructor(n: &BigNat) -> Expr {
    match n.pred() {
        None => Expr::const_(names::NAT_ZERO.clone(), vec![]),
        Some(pred) => Expr::app(
            Expr::const_(names::NAT_SUCC.clone(), vec![]),
            Expr::from_kind(ExprKind::Lit(Literal::Nat(pred))),
        ),
    }
}

/// Is `e` `Nat` zero (the `Nat.zero` constructor or the literal `0`)?
///
/// Mirrors `tc/reduction/nat.rs::is_nat_zero_expr` (Lean 4 `is_nat_zero`).
pub(super) fn is_nat_zero_expr(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Lit(Literal::Nat(n)) => n.is_zero(),
        ExprKind::Const(name, levels) => levels.is_empty() && *name == *names::NAT_ZERO,
        _ => false,
    }
}

/// If `e` is a `Nat` successor — `Nat.succ x` (an app) or a literal `n > 0` —
/// return the predecessor (`x`, or the literal `n-1`). Otherwise `None`.
///
/// Mirrors `tc/reduction/nat.rs::is_nat_succ_expr` (Lean 4 `is_nat_succ`).
pub(super) fn is_nat_succ_expr(e: &Expr) -> Option<Expr> {
    match &e.kind {
        ExprKind::Lit(Literal::Nat(n)) => {
            let pred = n.pred()?;
            Some(Expr::from_kind(ExprKind::Lit(Literal::Nat(pred))))
        }
        ExprKind::App(f, arg) => {
            if let ExprKind::Const(name, levels) = &f.kind {
                if levels.is_empty() && *name == *names::NAT_SUCC {
                    return Some(arg.as_ref().clone());
                }
            }
            None
        }
        _ => None,
    }
}

/// WHNF `e` then extract its closed `BigNat` value, peeling any `Nat.succ`
/// spine ITERATIVELY (so a long `Nat.succ (Nat.succ … )` chain does not grow
/// the native stack per layer). Returns `None` for non-closed `Nat`s.
///
/// `whnf` is the caller's WHNF (the verifier's full WHNF, or the builder's
/// simplified one). Mirrors `tc/reduction/nat.rs::get_nat_bignat_whnf`.
fn get_nat_bignat(e: &Expr, whnf: &dyn Fn(&Expr) -> Expr) -> Option<BigNat> {
    let mut succs = BigNat::Small(0);
    let mut cur = e.clone();
    loop {
        // Peel a SYNTACTIC `Nat.succ x` head without re-entering WHNF.
        if let ExprKind::App(f, arg) = &cur.kind {
            if let ExprKind::Const(name, levels) = &f.kind {
                if levels.is_empty() && *name == *names::NAT_SUCC {
                    succs = succs.checked_add_big(&BigNat::Small(1));
                    cur = arg.as_ref().clone();
                    continue;
                }
            }
        }
        // Head is not a syntactic succ-app: reduce once and inspect.
        let cur_whnf = whnf(&cur);
        match &cur_whnf.kind {
            ExprKind::Lit(Literal::Nat(n)) => return Some(succs.checked_add_big(n)),
            ExprKind::Const(name, levels) if levels.is_empty() && *name == *names::NAT_ZERO => {
                return Some(succs);
            }
            ExprKind::App(f, _) => {
                if let ExprKind::Const(name, levels) = &f.kind {
                    if levels.is_empty() && *name == *names::NAT_SUCC {
                        cur = cur_whnf;
                        continue;
                    }
                }
                return None;
            }
            _ => return None,
        }
    }
}

/// Reduce a binary closed-`Nat` arithmetic op to a literal (or `None` if either
/// operand is not a closed `Nat`, or `op` declines, e.g. an out-of-bound mul).
fn reduce_bin(
    a1: &Expr,
    a2: &Expr,
    whnf: &dyn Fn(&Expr) -> Expr,
    op: impl FnOnce(&BigNat, &BigNat) -> Option<BigNat>,
) -> Option<Expr> {
    let v1 = get_nat_bignat(a1, whnf)?;
    let v2 = get_nat_bignat(a2, whnf)?;
    op(&v1, &v2).map(Expr::bignat_lit)
}

/// Reduce a binary closed-`Nat` predicate to `Bool.true`/`Bool.false`.
fn reduce_pred(
    a1: &Expr,
    a2: &Expr,
    whnf: &dyn Fn(&Expr) -> Expr,
    pred: impl FnOnce(&BigNat, &BigNat) -> bool,
) -> Option<Expr> {
    let v1 = get_nat_bignat(a1, whnf)?;
    let v2 = get_nat_bignat(a2, whnf)?;
    let name = if pred(&v1, &v2) {
        names::BOOL_TRUE.clone()
    } else {
        names::BOOL_FALSE.clone()
    };
    Some(Expr::const_(name, vec![]))
}

/// Reduce closed `Nat` arithmetic on `e` to a literal, if `e`'s head is a known
/// `Nat` op constant applied to closed-`Nat` operands. `None` otherwise.
///
/// Mirrors `tc/reduction/nat.rs::reduce_nat` (Lean 4 `reduce_nat`), restricted
/// to arbitrary-precision arithmetic via `BigNat`. Bounded ops (`mul`, `pow`,
/// `shiftLeft`) decline past their limb cap exactly as the main path does.
pub(super) fn reduce_nat(e: &Expr, whnf: &dyn Fn(&Expr) -> Expr) -> Option<Expr> {
    let nargs = e.get_app_num_args();

    if nargs == 1 {
        // Unary: `Nat.succ` of any closed `Nat`.
        if let ExprKind::App(f, arg) = &e.kind {
            if let ExprKind::Const(name, levels) = &f.kind {
                if levels.is_empty() && *name == *names::NAT_SUCC {
                    let v = get_nat_bignat(arg, whnf)?;
                    return Some(Expr::bignat_lit(v.checked_add_big(&BigNat::Small(1))));
                }
            }
        }
        return None;
    }

    if nargs == 2 {
        let ExprKind::App(f_a1, a2) = &e.kind else {
            return None;
        };
        let ExprKind::App(f, a1) = &f_a1.kind else {
            return None;
        };
        let ExprKind::Const(name, levels) = &f.kind else {
            return None;
        };
        if !levels.is_empty() {
            return None;
        }
        if *name == *names::NAT_ADD {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.checked_add_big(y)));
        }
        if *name == *names::NAT_SUB {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.saturating_sub_big(y)));
        }
        if *name == *names::NAT_MUL {
            return reduce_bin(a1, a2, whnf, |x, y| x.checked_mul_big(y));
        }
        if *name == *names::NAT_DIV {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.checked_div_big(y)));
        }
        if *name == *names::NAT_MOD {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.checked_mod_big(y)));
        }
        if *name == *names::NAT_GCD {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.gcd_big(y)));
        }
        if *name == *names::NAT_POW {
            return reduce_bin(a1, a2, whnf, |x, y| x.checked_pow_big(y));
        }
        if *name == *names::NAT_BEQ {
            return reduce_pred(a1, a2, whnf, |x, y| x == y);
        }
        if *name == *names::NAT_BLE {
            return reduce_pred(a1, a2, whnf, |x, y| x <= y);
        }
        if *name == *names::NAT_LAND {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.bitand_big(y)));
        }
        if *name == *names::NAT_LOR {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.bitor_big(y)));
        }
        if *name == *names::NAT_XOR {
            return reduce_bin(a1, a2, whnf, |x, y| Some(x.bitxor_big(y)));
        }
        if *name == *names::NAT_SHIFT_LEFT {
            return reduce_bin(a1, a2, whnf, |x, y| {
                if x.is_zero() {
                    return Some(BigNat::Small(0));
                }
                let shift = y.to_u64()?;
                if shift > 1024 {
                    return None;
                }
                let result = x.checked_shl_big(shift as usize);
                if result.limbs().len() > 16 {
                    None
                } else {
                    Some(result)
                }
            });
        }
        if *name == *names::NAT_SHIFT_RIGHT {
            return reduce_bin(a1, a2, whnf, |x, y| {
                let shift = y.to_u64()?;
                if shift > u64::MAX / 2 {
                    return Some(BigNat::Small(0));
                }
                Some(x.shr_big(shift as usize))
            });
        }
        return None;
    }

    None
}

/// Structural `Nat` offset equality on two already-WHNF'd expressions.
///
/// * both zero            ⇒ `Some(true)`
/// * both successors       ⇒ `Some(eq_pred(pred t, pred s))` (recurse via the
///   caller-supplied predecessor def_eq)
/// * otherwise            ⇒ `None` (cannot decide via offset; caller falls back)
///
/// Mirrors `tc/reduction/nat.rs::is_def_eq_offset`. `eq_pred` is the caller's
/// full definitional-equality check (so the predecessors get the complete
/// engine, not just structural comparison).
pub(super) fn is_def_eq_offset(
    t: &Expr,
    s: &Expr,
    eq_pred: &dyn Fn(&Expr, &Expr) -> bool,
) -> Option<bool> {
    if is_nat_zero_expr(t) && is_nat_zero_expr(s) {
        return Some(true);
    }
    if let (Some(pred_t), Some(pred_s)) = (is_nat_succ_expr(t), is_nat_succ_expr(s)) {
        return Some(eq_pred(&pred_t, &pred_s));
    }
    None
}
