// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Native `Nat` literal reduction, metered (design §5.1, R166).

use super::*;

/// Native `Nat` literal reduction (design §5.1 "native Nat/String reduction").
/// Recognizes `Nat.succ (Lit n)` and the binary `Nat.{add,sub,mul,...}` ops on
/// two `Nat` literals, reducing them in arbitrary precision via [`crate::BigNat`]
/// (no fixed-width arithmetic on values). Anything else is `None` (stuck).
pub(super) fn try_native_nat(
    env: &dyn Env,
    ctx: &[Term],
    head: &Term,
    args: &[Term],
    budget: &mut Budget,
) -> Result<Option<Term>, BudgetError> {
    let TermKind::Const(cref) = head.kind() else {
        return Ok(None);
    };
    let name = cref.name();
    if !env.native_nat_allowed(name) {
        return Ok(None);
    }
    // Only Lean's own level-free `Nat.<op>` constants participate: pinned Lean
    // compares the head with each exact constant (`f == *g_nat_add`, …), so a
    // user's `Foo.Nat.add` is an ordinary constant, unfolded by δ (R166).
    if !cref.levels().is_empty() || name.parent() != Some(Name::from_dotted("Nat")) {
        return Ok(None);
    }
    let op = match name.last_str() {
        Some(op) => op,
        None => return Ok(None),
    };
    // Nat.succ n  ~>  Lit(n+1)
    if op == "succ" {
        let [arg] = args else { return Ok(None) };
        let arg = whnf_in_context(env, ctx, arg, budget)?;
        if let Some(n) = nat_lit(&arg) {
            let one = crate::BigNat::one();
            budget.charge(crate::bignat::result_words::sum(&n, &one))?;
            return Ok(Some(Term::lit(Lit::Nat(n.add(&one)))));
        }
        return Ok(None);
    }
    // Binary ops on two literals.
    let bin: Option<fn(&crate::BigNat, &crate::BigNat) -> NatResult> = match op {
        "add" => Some(|a, b| NatResult::Nat(a.add(b))),
        "sub" => Some(|a, b| NatResult::Nat(a.sub(b))),
        "mul" => Some(|a, b| NatResult::Nat(a.mul(b))),
        "div" => Some(|a, b| NatResult::Nat(a.div(b))),
        "mod" => Some(|a, b| NatResult::Nat(a.rem(b))),
        // Pinned Lean reduces `Nat.pow` only for an exponent up to 2^24 (R166;
        // clean-kernel's TypeChecker is stricter: an exponent up to 1023 and
        // products up to 256 limbs); past it the application stays stuck.
        "pow" => Some(|a, b| match b.as_u64() {
            Some(k) if k <= MAX_NATIVE_POW_EXPONENT => NatResult::Nat(a.pow(b)),
            _ => NatResult::Stuck,
        }),
        "beq" => Some(|a, b| NatResult::Bool(a.dec_eq(b))),
        "ble" => Some(|a, b| NatResult::Bool(a.dec_le(b))),
        // The rest of Lean's kernel `Nat` extensions (R162; the 14 names of
        // clean-kernel's `LEAN_KERNEL_NAT_EXTENSIONS`).
        "gcd" => Some(|a, b| NatResult::Nat(nat_gcd(a, b))),
        "land" => Some(|a, b| NatResult::Nat(big(a.as_biguint() & b.as_biguint()))),
        "lor" => Some(|a, b| NatResult::Nat(big(a.as_biguint() | b.as_biguint()))),
        "xor" => Some(|a, b| NatResult::Nat(big(a.as_biguint() ^ b.as_biguint()))),
        // Pinned Lean bounds no shift; the work meter pays for the result
        // first (R166). A shift past `u64` stays stuck: no literal could hold it.
        "shiftLeft" => Some(|a, b| match b.as_u64() {
            Some(_) if a.is_zero() => NatResult::Nat(crate::BigNat::zero()),
            Some(k) => NatResult::Nat(big(std::ops::Shl::shl(a.as_biguint(), k))),
            None => NatResult::Stuck,
        }),
        "shiftRight" => Some(|a, b| match b.as_u64() {
            Some(k) => NatResult::Nat(big(std::ops::Shr::shr(a.as_biguint(), k))),
            // A shift past every bit of any literal ck0 holds is 0.
            None => NatResult::Nat(crate::BigNat::zero()),
        }),
        _ => None,
    };
    let Some(bin) = bin else { return Ok(None) };
    let [a0, a1] = args else { return Ok(None) };
    let a0 = whnf_in_context(env, ctx, a0, budget)?;
    let a1 = whnf_in_context(env, ctx, a1, budget)?;
    match (nat_lit(&a0), nat_lit(&a1)) {
        (Some(x), Some(y)) => {
            // The work meter: the result's size is paid for before it is built.
            budget.charge(native_result_words(op, &x, &y))?;
            Ok(match bin(&x, &y) {
                NatResult::Nat(n) => Some(Term::lit(Lit::Nat(n))),
                NatResult::Bool(b) => Some(bool_term(b)),
                NatResult::Stuck => None,
            })
        }
        _ => Ok(None),
    }
}

/// The work meter's charge for the native `Nat` operation `op` on `a` and `b`
/// (R166), in 64-bit words. Reading the operands copies them (`nat_lit`), so
/// every operation, a comparison or a stuck application included, is charged at
/// least the larger operand's size plus one, half the copy's at worst. Beyond
/// that the charge bounds the result's size, so a
/// decision's native arithmetic allocates at most as many words as its fuel
/// (without it one `Nat.pow` of a large base to an exponent under Lean's bound
/// asks for a result of 2^48 bits). `/`, `%` and `gcd` return a small result
/// after quadratic work (schoolbook division; Euclid's loop of remainders), so
/// they are charged the product of their operands' sizes, which bounds their
/// time per unit of fuel by a constant. Multiplication, and `pow`'s squarings,
/// take time superlinear in the result's size (num-bigint's Karatsuba and
/// Toom-3, below schoolbook's quadratic) and are charged that size only:
/// charging their work would refuse products that Lean computes at once.
pub(super) fn native_result_words(op: &str, a: &crate::BigNat, b: &crate::BigNat) -> u64 {
    use crate::bignat::result_words;
    let result = match op {
        "mul" => result_words::product(a, b),
        "div" | "mod" | "gcd" => result_words::division_work(a, b),
        "pow" => match b.as_u64() {
            Some(k) if k <= MAX_NATIVE_POW_EXPONENT => result_words::power(a, k),
            _ => 1,
        },
        "shiftLeft" => match b.as_u64() {
            Some(k) => result_words::shifted_left(a, k),
            None => 1,
        },
        _ => 1,
    };
    result_words::sum(a, b).max(result)
}

/// `Nat.pow a b` is computed only for `b` up to this: pinned Lean's
/// `ReducePowMaxExp` (`1<<24`; `reduce_pow` returns none when `v2 >` it). A larger
/// exponent leaves the application stuck, as in Lean (R166). The size of what a
/// smaller one computes is bounded by the work meter, [`native_result_words`].
pub(super) const MAX_NATIVE_POW_EXPONENT: u64 = 1 << 24;

pub(super) fn big(n: num_bigint::BigUint) -> crate::BigNat {
    crate::BigNat::from_biguint(n)
}

/// `Nat.gcd` (Euclid; `gcd 0 b = b`, `gcd a 0 = a`).
pub(super) fn nat_gcd(a: &crate::BigNat, b: &crate::BigNat) -> crate::BigNat {
    let (mut x, mut y) = (a.clone(), b.clone());
    while !y.is_zero() {
        let r = x.rem(&y);
        x = y;
        y = r;
    }
    x
}

enum NatResult {
    Nat(crate::BigNat),
    Bool(bool),
    /// Not computed natively (the application stays stuck).
    Stuck,
}

/// `Bool.true` / `Bool.false` as 0-level `Const`s (the corpus `Bool` ctors).
pub(super) fn bool_term(b: bool) -> Term {
    let name = if b {
        Name::from_dotted("Bool.true")
    } else {
        Name::from_dotted("Bool.false")
    };
    // These constructors are nullary and level-param-free; we mint the bare
    // ConstRef directly (the native reducer is trusted TCB, design §3.2).
    Term::native_const(name)
}

/// Extract a `Nat` value from a whnf'd term: a literal, or the constant
/// `Nat.zero` with no universe levels, which is `0`. Pinned Lean's native
/// reductions read their arguments the same way (`is_nat_lit_ext`, `e ==
/// *g_nat_zero || is_nat_lit(e)`), so `Nat.succ Nat.zero` reduces to `1` (R166).
/// Conversion already reads `Lit 0 ≡ Nat.zero` (`def_eq.rs`).
pub(super) fn nat_lit(t: &Term) -> Option<crate::BigNat> {
    match t.kind() {
        TermKind::Lit(Lit::Nat(n)) => Some(n.clone()),
        TermKind::Const(c)
            if c.levels().is_empty() && *c.name() == Name::from_dotted("Nat.zero") =>
        {
            Some(crate::BigNat::zero())
        }
        _ => None,
    }
}
