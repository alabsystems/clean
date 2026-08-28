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

// ═══════════════════════════════════════════════════════════════════════════
// Native `Int`-predecessor fold: `Nat.rec (fun _ => Int) z pred N  ↝  z − N`
// ═══════════════════════════════════════════════════════════════════════════

/// Iteration count at or above which the closed `Int`-predecessor fold is
/// computed natively instead of ι-expanded one step at a time.
///
/// `2^9 = 512`, the same constant and rationale as the two native-`Nat` grind
/// guards (`native_nat_binop_grind_stuck`, `native_nat_grind_recursor_stuck`):
/// comfortably above any count a legitimate definitional proof unfolds by hand,
/// and at-or-below every perf-class grind. **Below the threshold this reducer
/// declines without touching a single operand**, so every small fold in the
/// existing corpus keeps a bit-identical reduction order and normal form.
const INT_PRED_FOLD_MIN_ITERATIONS: u64 = 1 << 9;

impl TypeChecker<'_> {
    /// Compute a **closed `Int`-predecessor fold** in O(limbs) instead of
    /// Θ(count) unary ι-steps.
    ///
    /// Fires iff `e` is exactly
    ///
    /// ```text
    /// Nat.rec (fun _ : Nat => Int)
    ///         z
    ///         (fun (_ : Nat) (ih : Int) =>
    ///            Int.rec (fun _ : Int => Int)
    ///                    (fun a : Nat => Nat.rec (fun _ : Nat => Int)
    ///                                            (Int.negSucc Nat.zero)
    ///                                            (fun m _ => Int.ofNat m)
    ///                                            a)
    ///                    (fun b : Nat => Int.negSucc (Nat.succ b))
    ///                    ih)
    ///         N
    /// ```
    ///
    /// with `N` a closed `Nat` literal `>= INT_PRED_FOLD_MIN_ITERATIONS` and `z`
    /// WHNF-reducing to a closed `Int`. The result is the constructor literal
    /// for `z − N`.
    ///
    /// # Why this exists (measured)
    ///
    /// `import Init.GrindInstances` re-checks the `Int32`/`Int64`/`BitVec`
    /// conversion lemmas, whose `toInt` bodies are `↑(toBitVec.toNat) − 2^32`
    /// (resp. `2^64`) *elaborated as this fold*. Measured 2026-08-26 at
    /// `69f4f4a70`: **599,888 of 600,000** ι-expansions over a large literal in
    /// that import are this exact recursor, the count decrementing by exactly 1
    /// per expansion from `2^32`, i.e. ~4.3 billion steps — the run reached
    /// 10.4 GB RSS in 13 s and was killed. Lean evaluates the same term in O(1)
    /// through GMP.
    ///
    /// # SOUNDNESS
    ///
    /// This reducer **mints a value**, so the match must *determine* the folded
    /// function rather than merely suggest it. Two things make it exact.
    ///
    /// 1. **The step function is pinned by exhaustive case analysis.** Every
    ///    node of the minor premise is matched — no wildcards, no "head is
    ///    `Int.rec`, trust the rest". Given the match, for every closed `v : Int`:
    ///    - `v = Int.ofNat 0`   → `Nat.rec … Nat.zero` = `Int.negSucc 0` = `−1`
    ///    - `v = Int.ofNat (m+1)` → `Int.ofNat m` = `v − 1`
    ///    - `v = Int.negSucc b` (= `−(b+1)`) → `Int.negSucc (b+1)` = `v − 1`
    ///
    ///    `Int` has exactly these two constructors (checked against the
    ///    environment below), so `step v = v − 1` for **all** `v`, and the outer
    ///    `Nat.rec` therefore denotes `z − N` by induction on `N`. The bound
    ///    `n : Nat` provably does not occur in the body: the match pins every
    ///    `BVar` occurrence in the tree, and each is the `ih`.
    ///
    /// 2. **The recursors are pinned to the standard ones.** `Nat.rec` and
    ///    `Int.rec` are checked in the environment for the standard shape *and
    ///    constructor-to-minor association* (`std_two_ctor_rec`), so a shadowed
    ///    or reordered `Int` cannot be mistaken for the real one.
    ///
    /// Every failure mode is a decline (`None`), which leaves the ordinary ι
    /// path untouched. The minted term is the same value the ι chain converges
    /// to, in the canonical literal form `mk_int_expr` already produces for
    /// `reduce_int`.
    pub(in crate::tc) fn reduce_int_pred_fold(
        &self,
        e: &Expr,
        rec_name: &crate::name::Name,
    ) -> Option<Expr> {
        if *rec_name != *names::NAT_REC {
            return None;
        }
        if e.get_app_num_args() != 4 {
            return None;
        }
        let args = e.get_app_args();
        // Motive must be `fun _ : Nat => Int` — an Int-valued fold.
        if !is_const_motive(args[0], &names::INT) {
            return None;
        }
        // The minor premise must be exactly the Int predecessor (see SOUNDNESS).
        if !is_int_pred_step(args[2]) {
            return None;
        }
        // Both recursors must be the standard ones, with the standard
        // constructor-to-minor association.
        if !self.std_two_ctor_rec(
            &names::NAT_REC,
            &names::NAT,
            &names::NAT_ZERO,
            0,
            &names::NAT_SUCC,
            1,
        ) || !self.std_two_ctor_rec(
            &names::INT_REC,
            &names::INT,
            &names::INT_OF_NAT,
            1,
            &names::INT_NEG_SUCC,
            1,
        ) {
            return None;
        }
        // Iteration count: a closed literal at or above the threshold. Below it
        // we decline WITHOUT having touched `z`, so small folds are unperturbed.
        let count = self.get_nat_bignat_whnf_pub(args[3])?;
        if matches!(&count, BigNat::Small(v) if *v < INT_PRED_FOLD_MIN_ITERATIONS) {
            return None;
        }
        // Accumulator: must WHNF to a closed `Int`.
        let z = self.get_int_whnf(args[1])?;
        let result = int_add(
            &z,
            &IntVal {
                neg: true,
                mag: count,
            },
        );
        Some(mk_int_expr(result))
    }

    /// Is `rec` the environment's recursor for a standard non-parametric,
    /// non-indexed, two-constructor inductive `ind`, whose minor premises are in
    /// the order `c0` (with `f0` fields) then `c1` (with `f1` fields)?
    ///
    /// This is what lets `reduce_int_pred_fold` read a minor premise *positionally*
    /// and still know which constructor it computes on.
    fn std_two_ctor_rec(
        &self,
        rec: &crate::name::Name,
        ind: &crate::name::Name,
        c0: &crate::name::Name,
        f0: u32,
        c1: &crate::name::Name,
        f1: u32,
    ) -> bool {
        let Some(rv) = self.env.get_recursor(rec) else {
            return false;
        };
        rv.inductive_name == *ind
            && rv.arg_order == crate::inductive::RecursorArgOrder::MajorAfterMinors
            && rv.num_params == 0
            && rv.num_indices == 0
            && rv.num_motives == 1
            && rv.num_minors == 2
            && !rv.is_k
            && rv.rules.len() == 2
            && rv.rules[0].constructor_name == *c0
            && rv.rules[0].num_fields == f0
            && rv.rules[1].constructor_name == *c1
            && rv.rules[1].num_fields == f1
    }
}

/// Strip `MData` annotations, which are reduction-transparent.
fn peel(e: &Expr) -> &Expr {
    let mut cur = e;
    while let ExprKind::MData(_, inner) = cur.kind() {
        cur = inner;
    }
    cur
}

fn is_const(e: &Expr, name: &crate::name::Name) -> bool {
    matches!(peel(e).kind(), ExprKind::Const(n, _) if *n == *name)
}

fn is_bvar(e: &Expr, idx: u32) -> bool {
    matches!(peel(e).kind(), ExprKind::BVar(i) if *i == idx)
}

/// `fun _ => <Const name>` — a constant motive returning the type `name`.
/// The body is a bare `Const`, so the bound variable provably does not occur.
fn is_const_motive(e: &Expr, name: &crate::name::Name) -> bool {
    match peel(e).kind() {
        ExprKind::Lam(_, _, body) => is_const(body, name),
        _ => false,
    }
}

/// `Nat.zero` or the literal `0` — both denote zero.
fn is_nat_zero(e: &Expr) -> bool {
    match peel(e).kind() {
        ExprKind::Lit(Literal::Nat(n)) => n.is_zero(),
        _ => is_const(e, &names::NAT_ZERO),
    }
}

/// Match a spine `f a1 … ak` whose head is `Const name`, returning the args.
fn app_of_const<'a>(
    e: &'a Expr,
    name: &crate::name::Name,
    arity: usize,
) -> Option<smallvec::SmallVec<[&'a Expr; 8]>> {
    let e = peel(e);
    if !matches!(e.kind(), ExprKind::App(..)) {
        return None;
    }
    if !is_const(e.get_app_fn(), name) {
        return None;
    }
    let args = e.get_app_args();
    if args.len() != arity {
        return None;
    }
    Some(args)
}

/// Is `s` exactly `fun (_ : Nat) (ih : Int) => ih − 1`, written as the `Int.rec`
/// case split the elaborator emits? See `reduce_int_pred_fold`'s SOUNDNESS note
/// — this match pins every node, which is what makes the fold's value derivable.
fn is_int_pred_step(s: &Expr) -> bool {
    // fun (_ : Nat) => fun (ih : Int) => body   (ih is BVar 0 inside `body`)
    let ExprKind::Lam(_, _, inner) = peel(s).kind() else {
        return false;
    };
    let ExprKind::Lam(_, _, body) = peel(inner).kind() else {
        return false;
    };
    // Int.rec (fun _ : Int => Int) <ofNat case> <negSucc case> ih
    let Some(rec_args) = app_of_const(body, &names::INT_REC, 4) else {
        return false;
    };
    if !is_const_motive(rec_args[0], &names::INT) || !is_bvar(rec_args[3], 0) {
        return false;
    }
    is_of_nat_pred_case(rec_args[1]) && is_neg_succ_pred_case(rec_args[2])
}

/// `fun (a : Nat) => Nat.rec (fun _ : Nat => Int) (Int.negSucc Nat.zero)
///                           (fun (m : Nat) (_ : Int) => Int.ofNat m) a`
///
/// i.e. `Int.ofNat a − 1`: zero ↦ `−1`, `m+1` ↦ `Int.ofNat m`.
fn is_of_nat_pred_case(e: &Expr) -> bool {
    let ExprKind::Lam(_, _, body) = peel(e).kind() else {
        return false;
    };
    let Some(args) = app_of_const(body, &names::NAT_REC, 4) else {
        return false;
    };
    // motive `fun _ : Nat => Int`; major is the bound `a` (BVar 0).
    if !is_const_motive(args[0], &names::INT) || !is_bvar(args[3], 0) {
        return false;
    }
    // zero case: `Int.negSucc Nat.zero` = −1.
    let Some(zero_case) = app_of_const(args[1], &names::INT_NEG_SUCC, 1) else {
        return false;
    };
    if !is_nat_zero(zero_case[0]) {
        return false;
    }
    // succ case: `fun (m : Nat) (_ : Int) => Int.ofNat m`. Inside the two
    // binders `m` is BVar 1, so the induction hypothesis is provably unused.
    let ExprKind::Lam(_, _, inner) = peel(args[2]).kind() else {
        return false;
    };
    let ExprKind::Lam(_, _, succ_body) = peel(inner).kind() else {
        return false;
    };
    match app_of_const(succ_body, &names::INT_OF_NAT, 1) {
        Some(a) => is_bvar(a[0], 1),
        None => false,
    }
}

/// `fun (b : Nat) => Int.negSucc (Nat.succ b)`
///
/// i.e. `Int.negSucc b − 1`: `−(b+1) − 1 = −(b+2)`.
fn is_neg_succ_pred_case(e: &Expr) -> bool {
    let ExprKind::Lam(_, _, body) = peel(e).kind() else {
        return false;
    };
    let Some(neg) = app_of_const(body, &names::INT_NEG_SUCC, 1) else {
        return false;
    };
    match app_of_const(neg[0], &names::NAT_SUCC, 1) {
        Some(s) => is_bvar(s[0], 0),
        None => false,
    }
}
