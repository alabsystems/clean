// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arbitrary-precision `Int` literal reduction for the type checker.
//!
//! Parallels `reduction::nat` for `Nat`. The env-level native `Int.*` reducers
//! (`native_reducers_int`) operate on arguments that are ALREADY constructor
//! literals (`Int.ofNat n` / `Int.negSucc n`); they do NOT whnf their operands.
//! That is fine on the hot path, but the `Rat.le` quotient lift produces
//! operands like
//!
//! ```text
//! Int.mul (Rat.Raw.num (Rat.Raw.mk …)) (Int.ofNat (Rat.Raw.effDenom (Rat.Raw.mk …)))
//! ```
//!
//! whose operands are PROJECTIONS, not yet literals. The native reducer then
//! declines and the kernel δ-unfolds the recursive `Int.mul` definition to
//! `Int.ofNat (Nat.mul …)` over un-reduced projection arguments — and the
//! ensuing `is_def_eq`/`whnf` work explodes with the denominator magnitude (the
//! "Rat-blowup wall" at the binary64 `2^1074` floored-ulp scale, even after the
//! `Nat.pred` OOM wall is closed).
//!
//! `reduce_int` fires in the WHNF App pre-check BEFORE δ-unfolding, exactly like
//! `reduce_nat`. It WHNF-reduces each operand to a closed `Int` (peeling
//! `Int.ofNat`/`Int.negSucc` after whnf), then computes `add`/`sub`/`mul` on
//! arbitrary-precision sign-magnitude BigNats — so the `Rat.le` cross-products
//! and difference reduce in O(limbs), never δ-unfolding the recursive `Int`
//! arithmetic. ZERO soundness effect: it is pure evaluation matching the `Int`
//! constructor semantics (`Int.ofNat n`, `Int.negSucc n = −(n+1)`), the same
//! values the recursive definitions compute.

use super::names;
use crate::expr::{BigNat, Expr, ExprKind, Literal};
use crate::tc::TypeChecker;

/// A closed `Int` as sign-magnitude: value `(-1)^neg · mag`.
struct IntVal {
    neg: bool,
    mag: BigNat,
}

/// Result-limb cap for `Int.mul` (≈5120 bits). Bounds allocation while covering
/// the `Rat.le` cross-products at the `2^1074` scale (≈34-limb products). Same
/// bound as the env-level BigInt reducer (`native_reducers_int::BIGINT_LIMB_CAP`).
const INT_LIMB_CAP: usize = 80;

impl<'env> TypeChecker<'env> {
    /// Reduce closed `Int` arithmetic (`Int.add`/`Int.sub`/`Int.mul`) to a
    /// constructor literal, WHNF-reducing operands first.
    ///
    /// Returns `None` when the head is not one of these binary `Int` ops, when
    /// an operand does not WHNF to a closed `Int`, or when a product exceeds the
    /// limb cap (declines rather than over-allocates — sound: no reduction).
    pub(in crate::tc) fn reduce_int(&self, e: &Expr) -> Option<Expr> {
        if e.get_app_num_args() != 2 {
            return None;
        }
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
        let is_add = *name == *names::INT_ADD;
        let is_sub = *name == *names::INT_SUB;
        let is_mul = *name == *names::INT_MUL;
        if !(is_add || is_sub || is_mul) {
            return None;
        }
        // SCOPE GUARD (non-regression) — fire ONLY when the expression
        // SYNTACTICALLY contains a `Big` Nat literal (a magnitude exceeding
        // `u64`). That is PRECISELY the case the established env-level i128
        // `Int.*` reducers cannot handle and the only case this reducer exists
        // for: the `Rat.le` cross-products at the binary64 floored-ulp scale
        // (`2^1074`, ~17 limbs — present verbatim as the `Rat.Raw.mk`
        // denominator). For every all-small-`Int` term — i.e. the ENTIRE
        // existing proof corpus — this declines WITHOUT touching the operands,
        // so the small-`Int` reduction order / normal forms (and the delicate
        // `Rat.ble` / `Eq.subst`-motive def-eq comparisons that depend on them)
        // stay BIT-IDENTICAL to before this reducer existed. Cheap: a bounded
        // structural scan, no WHNF, no δ.
        if !contains_big_nat_lit(e) {
            return None;
        }
        let x = self.get_int_whnf(a1)?;
        let y = self.get_int_whnf(a2)?;
        let result = if is_add {
            int_add(&x, &y)
        } else if is_sub {
            int_add(
                &x,
                &IntVal {
                    neg: !y.neg,
                    mag: y.mag.clone(),
                },
            )
        } else {
            int_mul(&x, &y)?
        };
        Some(mk_int_expr(result))
    }

    /// WHNF-reduce `e` then extract its closed `Int` value (sign-magnitude).
    ///
    /// Recognises the constructor heads after WHNF:
    /// - `Int.ofNat n`   → `(+, n)`
    /// - `Int.negSucc n` → `(−, n+1)`
    /// - a bare `Nat` literal (un-normalized `Int.ofNat`) → `(+, n)`
    ///
    /// `n` is itself WHNF-extracted as an arbitrary-precision `BigNat` via the
    /// Nat path (`get_nat_bignat_whnf`), so a `Nat.succ (Nat.pred …)` effDenom
    /// argument collapses to a literal here (using the native `Nat.pred`/`succ`
    /// reducers) before the Int operation is applied.
    fn get_int_whnf(&self, e: &Expr) -> Option<IntVal> {
        let w = self.whnf_impl(e);
        match &w.kind {
            ExprKind::App(f, arg) => {
                let ExprKind::Const(name, levels) = &f.kind else {
                    return None;
                };
                if !levels.is_empty() {
                    return None;
                }
                if *name == *names::INT_OF_NAT {
                    let n = self.get_nat_bignat_whnf_pub(arg)?;
                    Some(IntVal { neg: false, mag: n })
                } else if *name == *names::INT_NEG_SUCC {
                    let n = self.get_nat_bignat_whnf_pub(arg)?;
                    // negSucc n = −(n+1).
                    Some(IntVal {
                        neg: true,
                        mag: n.checked_add_big(&BigNat::Small(1)),
                    })
                } else {
                    None
                }
            }
            ExprKind::Lit(Literal::Nat(n)) => Some(IntVal {
                neg: false,
                mag: n.clone(),
            }),
            _ => None,
        }
    }
}

/// Magnitude threshold (`2^21`) above which a `Nat` literal makes the default
/// reduction of an enclosing `Int.*` op (δ-unfold → `Nat.mul`/`Nat.rec`, or the
/// 16-limb-capped native `Nat.mul` declining → δ-unfold) prohibitively expensive
/// — the "Rat-blowup" regime. The discharge scales `2^24` (f32), `2^53` (f64),
/// `2^1074` (binary64 floored ulp) are all far above it; the existing proof
/// corpus's literals (≤ ~`2^20`, e.g. the `260577/4096` boolean-analysis
/// fractions) are all below it, so they keep their established (cheap, in-budget)
/// reduction path untouched. Chosen as the clean power-of-two gap between the two.
const RAT_BLOWUP_LIT_THRESHOLD: u64 = 1 << 21;

/// Does `e` syntactically contain a `Nat` literal at or above the
/// `RAT_BLOWUP_LIT_THRESHOLD` (incl. any `Big` literal, which exceeds `u64`)?
///
/// A bounded structural scan over the application spine / projections / binders
/// (depth-capped to stay cheap on the hot path). This is the scope guard for
/// `reduce_int`: it fires the arbitrary-precision Int reducer ONLY in the
/// large-literal "blowup" regime that needs it (the `Rat.le` cross-products at
/// the f32/f64/`2^1074` floored-ulp scales), and declines — WITHOUT touching the
/// operands — for every smaller term, leaving the existing small-`Int` reduction
/// order, normal forms, and heartbeat budget BIT-IDENTICAL to before.
fn contains_big_nat_lit(e: &Expr) -> bool {
    fn go(e: &Expr, depth: u32) -> bool {
        if depth == 0 {
            // Cap recursion; conservatively assume a deeper term MIGHT carry a
            // large literal so we don't miss the blowup case. (Firing on a false
            // positive is still sound — it just reduces a closed Int.)
            return true;
        }
        match e.kind() {
            ExprKind::Lit(Literal::Nat(n)) => match n.to_u64() {
                Some(v) => v >= RAT_BLOWUP_LIT_THRESHOLD,
                None => true, // `Big` (> u64): always in the blowup regime.
            },
            ExprKind::App(f, a) => go(f, depth - 1) || go(a, depth - 1),
            ExprKind::Proj(_, _, x) => go(x, depth - 1),
            ExprKind::Lam(_, ty, b) | ExprKind::Pi(_, ty, b) => {
                go(ty, depth - 1) || go(b, depth - 1)
            }
            ExprKind::Let(_, ty, v, b, _) => {
                go(ty, depth - 1) || go(v, depth - 1) || go(b, depth - 1)
            }
            _ => false,
        }
    }
    // Depth 64 comfortably covers the `Int.(add|sub|mul)` spines the `Rat.le`
    // lift builds over `Rat.Raw.mk`/`Int.ofNat`/`Rat.Raw.num`/`effDenom`.
    go(e, 64)
}

/// `a + b` over sign-magnitude `Int`s.
fn int_add(a: &IntVal, b: &IntVal) -> IntVal {
    if a.neg == b.neg {
        IntVal {
            neg: a.neg,
            mag: a.mag.checked_add_big(&b.mag),
        }
    } else {
        match a.mag.cmp(&b.mag) {
            std::cmp::Ordering::Equal => IntVal {
                neg: false,
                mag: BigNat::Small(0),
            },
            std::cmp::Ordering::Greater => IntVal {
                neg: a.neg,
                mag: a.mag.saturating_sub_big(&b.mag),
            },
            std::cmp::Ordering::Less => IntVal {
                neg: b.neg,
                mag: b.mag.saturating_sub_big(&a.mag),
            },
        }
    }
}

/// `a · b` over sign-magnitude `Int`s; `None` past the limb cap.
fn int_mul(a: &IntVal, b: &IntVal) -> Option<IntVal> {
    let mag = a.mag.mul_big_capped(&b.mag, INT_LIMB_CAP)?;
    let neg = (a.neg != b.neg) && !mag.is_zero();
    Some(IntVal { neg, mag })
}

/// Emit a sign-magnitude `Int` as a constructor application:
/// non-negative → `Int.ofNat mag`; negative → `Int.negSucc (mag − 1)`.
fn mk_int_expr(v: IntVal) -> Expr {
    if v.neg && !v.mag.is_zero() {
        let pred = v.mag.pred().unwrap_or(BigNat::Small(0));
        Expr::app(
            Expr::const_(names::INT_NEG_SUCC.clone(), vec![]),
            Expr::bignat_lit(pred),
        )
    } else {
        Expr::app(
            Expr::const_(names::INT_OF_NAT.clone(), vec![]),
            Expr::bignat_lit(v.mag),
        )
    }
}
