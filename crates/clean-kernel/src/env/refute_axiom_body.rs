// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Small-N refutation gate for FRIEDGUT-shaped admitted-axiom bodies (C4 gap fix).
//!
//! # Why this exists
//!
//! The carrier-generic C4 engine (`carrier_refutation::is_refutable`) has a
//! documented BLIND SPOT for the Friedgut-class body
//!
//! ```text
//! ∀ n f K eps,  I[f] ≤ K  →  0 ≤ eps  →
//!   ∀ (e : Nat),  natCast(2^e)·eps ≤ K  →
//!     ∃ (J : HCPoint n),  setSizeNat n J ≤ 2^(BUDGET e)
//!                       ∧ subsetSum n (fun S => ind(notSubsetMask n S J)·f̂(S)²) ≤ eps
//! ```
//!
//! that the fleet briefly installed as `friedgut_boolean_helper`'s value — a body
//! that is FALSE at `n = 2` (parity, `e = 0`), making `friedgut_boolean` a false
//! admitted axiom. C4 passed it anyway because it (a) does not enumerate a `BoolFn`
//! binder, (b) caps `Nat` witnesses at `{0,1,2}` and never instantiates the `∀ e`
//! guard with a hypothesis-SATISFYING value, and (c) cannot decide an
//! `∃ J, And(size, mass)` conclusion (it only handles `Rat.le`/`Eq`/`contains`).
//! See `designs/2026-06-20-friedgut-helper-body-FALSE-critical.md` and
//! `designs/2026-06-20-clean-tooling-wishlist.md` §P0.
//!
//! # What this module does
//!
//! It is a TARGETED refutation routine for exactly this shape. Given a candidate
//! body `Expr` of the friedgut form and a carrier-instantiation budget, it:
//!
//!   1. enumerates small `n` (≤ budget) and EXTREMAL Boolean functions `f`
//!      (parity/χ_S, dictator χ_i, AND/OR, constants),
//!   2. instantiates the universally-quantified scalars (`K`, `eps`) and the
//!      dyadic exponent `e` with small concrete `Rat`/`Nat` values that SATISFY
//!      the body's hypotheses (`I[f] ≤ K`, `0 ≤ eps`, `2^e·eps ≤ K`),
//!   3. for the `∃ J, And(|J| ≤ 2^(budget e), mass ≤ eps)` conclusion, ENUMERATES
//!      every `J : HCPoint n` (the `2^n` indicators) up to the size budget and
//!      kernel-REDUCES the `And` to check whether ANY `J` satisfies it,
//!   4. returns a concrete [`Counterexample`] `(n, f, K, eps, e)` when the
//!      hypotheses hold but NO admissible `J` satisfies the conclusion.
//!
//! All numeric facts are decided by the KERNEL's own reduction (`whnf` /
//! `is_def_eq` / the native `Rat`/`Nat`/`Bool` reducers) over CLOSED instances:
//! the routine builds the `Expr` instance and lets the kernel reduce the closed
//! `subsetSum`/`FourierCoefficient`/`setSizeNat`/`notSubsetMask` terms. It does
//! NOT re-implement any Fourier math in Rust, so a found counterexample is
//! faithful to the kernel's semantics.
//!
//! The routine is INTENTIONALLY conservative: it returns `None` ("no
//! counterexample found") whenever a closed instance fails to reduce to a
//! decidable comparison, so it never fabricates a refutation.

use super::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::name::Name;
use crate::tc::TypeChecker;

// ─────────────────────────── small term builders ───────────────────────────

/// `Nat.succ^k Nat.zero` (a closed `Nat` literal; small `k` only).
fn nat(k: u64) -> Expr {
    let mut e = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    for _ in 0..k {
        e = Expr::app(succ.clone(), e);
    }
    e
}

/// `Rat.mk (Int.ofNat num) denom` — the rational `num/denom`.
fn rat(num: u64, denom: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [
            Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                nat(num),
            ),
            nat(denom),
        ],
    )
}

/// `Fin n` index `⟨val, _⟩` built via the junk-tolerant `Fin.mk _ _ True`
/// constructor (Clean's faithful-`Fin` `isLt` slot is decided structurally; for
/// an in-range `val < n` any inhabitant suffices, and we only ever pass
/// `val < n`). Used to read/build cube coordinates.
fn fin_mk(n: u64, val: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Fin.mk"), vec![]),
        [
            nat(n),
            nat(val),
            Expr::const_(Name::from_string("True"), vec![]),
        ],
    )
}

/// `BoolAnalysis.HCPoint n` — the cube-point type `Fin n → Bool`.
fn hcpoint_ty(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("BoolAnalysis.HCPoint"), vec![]),
        nat(n),
    )
}

/// A concrete cube-point indicator `HCPoint n` from a `mask` bit-set: the point
/// `fun (i : Fin n) => <mask has bit (Fin.val i)>`, encoded WITHOUT recursion as
/// a chain of `Nat.beq (Fin.val i) k` selectors for each `k` with bit `k` set.
/// For the empty mask this is `fun _ => Bool.false`.
///
/// Concretely the body is, for set bits `k₀, k₁, …`:
/// `Bool.or (Nat.beq (Fin.val n i) k₀) (Bool.or (Nat.beq … k₁) … Bool.false)`.
/// Each `Nat.beq`/`Bool.or` is a reducible primitive, so the kernel evaluates
/// `point ⟨v⟩` to `Bool.true` iff bit `v` is set in `mask`.
fn hcpoint_from_mask(n: u64, mask: u64) -> Expr {
    let fin_n = Expr::app(Expr::const_(Name::from_string("Fin"), vec![]), nat(n));
    let fin_val = Expr::const_(Name::from_string("Fin.val"), vec![]);
    let nat_beq = Expr::const_(Name::from_string("Nat.beq"), vec![]);
    let bool_or = Expr::const_(Name::from_string("Bool.or"), vec![]);
    // `Fin.val n i` with `i` = BVar(0) under the λ.
    let val_i = Expr::apps(fin_val, [nat(n), Expr::bvar(0)]);
    let mut body = Expr::const_(Name::from_string("Bool.false"), vec![]);
    // Fold from the high bit down so the lowest set bit is outermost (order is
    // irrelevant to the Bool.or result; this just keeps it deterministic).
    for k in (0..n).rev() {
        if (mask >> k) & 1 == 1 {
            let is_k = Expr::apps(nat_beq.clone(), [val_i.clone(), nat(k)]);
            body = Expr::apps(bool_or.clone(), [is_k, body]);
        }
    }
    Expr::lam(BinderInfo::Default, fin_n, body)
}

// ───────────────────────── Boolean-function witnesses ─────────────────────────

/// A labelled extremal `BoolFn n = HCPoint n → Bool` witness.
struct BoolFnWitness {
    label: String,
    /// The closed `BoolFn n` term.
    func: Expr,
}

/// `fun (x : HCPoint n) => Bool.xor (… (Bool.xor (x ⟨0⟩) (x ⟨1⟩)) …) (x ⟨n-1⟩)` —
/// the PARITY function `⊕ᵢ xᵢ`. Its `{±1}` embedding `pm∘f` is the full parity
/// character `χ_{[n]}`, so `f̂(S) = δ_{S,[n]}`: all Fourier mass sits on the FULL
/// coordinate set. The extremal counterexample to any small-junta claim (every
/// junta `J ⊊ [n]` misses the full set, so the masked mass is the full `f̂([n])²`).
fn parity_fn(n: u64) -> Expr {
    let hcp = hcpoint_ty(n);
    let bool_xor = Expr::const_(Name::from_string("Bool.xor"), vec![]);
    // `x` is BVar(0) under the outer λ. `x ⟨i⟩`.
    let coord = |i: u64| Expr::app(Expr::bvar(0), fin_mk(n, i));
    let body = if n == 0 {
        // Empty parity = false (the identity of xor).
        Expr::const_(Name::from_string("Bool.false"), vec![])
    } else {
        let mut acc = coord(0);
        for i in 1..n {
            acc = Expr::apps(bool_xor.clone(), [acc, coord(i)]);
        }
        acc
    };
    Expr::lam(BinderInfo::Default, hcp, body)
}

/// `fun (x : HCPoint n) => x ⟨i⟩` — the DICTATOR on coordinate `i` (all mass at
/// level 1, set `{i}`).
fn dictator_fn(n: u64, i: u64) -> Expr {
    let hcp = hcpoint_ty(n);
    Expr::lam(
        BinderInfo::Default,
        hcp,
        Expr::app(Expr::bvar(0), fin_mk(n, i)),
    )
}

/// `fun (x : HCPoint n) => <const>` — a constant Boolean function.
fn const_fn(n: u64, b: &str) -> Expr {
    Expr::lam(
        BinderInfo::Default,
        hcpoint_ty(n),
        Expr::const_(Name::from_string(b), vec![]),
    )
}

/// `fun (x : HCPoint n) => Bool.and (x ⟨0⟩) (x ⟨1⟩) …` — the AND of all coords.
fn and_fn(n: u64) -> Expr {
    let hcp = hcpoint_ty(n);
    let bool_and = Expr::const_(Name::from_string("Bool.and"), vec![]);
    let coord = |i: u64| Expr::app(Expr::bvar(0), fin_mk(n, i));
    let body = if n == 0 {
        Expr::const_(Name::from_string("Bool.true"), vec![])
    } else {
        let mut acc = coord(0);
        for i in 1..n {
            acc = Expr::apps(bool_and.clone(), [acc, coord(i)]);
        }
        acc
    };
    Expr::lam(BinderInfo::Default, hcp, body)
}

/// `fun (x : HCPoint n) => Bool.or (x ⟨0⟩) (x ⟨1⟩) …` — the OR of all coords.
fn or_fn(n: u64) -> Expr {
    let hcp = hcpoint_ty(n);
    let bool_or = Expr::const_(Name::from_string("Bool.or"), vec![]);
    let coord = |i: u64| Expr::app(Expr::bvar(0), fin_mk(n, i));
    let body = if n == 0 {
        Expr::const_(Name::from_string("Bool.false"), vec![])
    } else {
        let mut acc = coord(0);
        for i in 1..n {
            acc = Expr::apps(bool_or.clone(), [acc, coord(i)]);
        }
        acc
    };
    Expr::lam(BinderInfo::Default, hcp, body)
}

/// The extremal `BoolFn n` witness battery for refutation: parity (the spread-out
/// extremal), the (up to 3) dictators, AND/OR, and the two constants.
fn boolfn_witnesses(n: u64) -> Vec<BoolFnWitness> {
    let mut ws = vec![BoolFnWitness {
        label: format!("parity(χ_[{n}])"),
        func: parity_fn(n),
    }];
    for i in 0..n.min(3) {
        ws.push(BoolFnWitness {
            label: format!("dictator[{i}]"),
            func: dictator_fn(n, i),
        });
    }
    ws.push(BoolFnWitness {
        label: "and".to_string(),
        func: and_fn(n),
    });
    ws.push(BoolFnWitness {
        label: "or".to_string(),
        func: or_fn(n),
    });
    ws.push(BoolFnWitness {
        label: "const-false".to_string(),
        func: const_fn(n, "Bool.false"),
    });
    ws.push(BoolFnWitness {
        label: "const-true".to_string(),
        func: const_fn(n, "Bool.true"),
    });
    ws
}

// ───────────────────────── closed-prop truth oracle ─────────────────────────

/// Spine-walk `e = c a1 a2 …` returning `(c-name, [a1, …])` if the head is a const.
fn const_app(e: &Expr) -> Option<(String, Vec<Expr>)> {
    let mut args = Vec::new();
    let mut cur = e;
    while let ExprKind::App(f, a) = cur.kind() {
        args.push((**a).clone());
        cur = f;
    }
    if let ExprKind::Const(n, _) = cur.kind() {
        args.reverse();
        Some((n.to_string(), args))
    } else {
        None
    }
}

/// Decode a closed `Nat` to its value by whnf-walking its `Nat.succ` spine (one
/// whnf per layer, no per-candidate `is_def_eq`), capped at a small bound so a
/// runaway term is reported `None` rather than looping. Handles both the `Nat.lit`
/// fast-path (a single whnf to the literal) and the `Nat.succ^k Nat.zero` tower.
fn decode_nat(tc: &TypeChecker, e: &Expr) -> Option<u64> {
    let mut cur = tc.whnf(e);
    let mut acc: u64 = 0;
    for _ in 0..=4096u64 {
        match cur.kind() {
            ExprKind::Const(n, _) if n.to_string() == "Nat.zero" => return Some(acc),
            ExprKind::Lit(crate::expr::Literal::Nat(v)) => {
                return v.to_u64().and_then(|v| acc.checked_add(v))
            }
            ExprKind::App(h, arg) => {
                if matches!(h.kind(), ExprKind::Const(nm, _) if nm.to_string() == "Nat.succ") {
                    acc = acc.checked_add(1)?;
                    cur = tc.whnf(arg);
                    continue;
                }
                return None;
            }
            _ => return None,
        }
    }
    None
}

/// Decode a CLOSED `Int` (`Int.ofNat k` / `Int.negSucc k`) reduced to its head
/// constructor, returning a signed value. `None` for a non-numeral Int.
fn decode_int(tc: &TypeChecker, e: &Expr) -> Option<i128> {
    let w = tc.whnf(e);
    let ExprKind::App(h, arg) = w.kind() else {
        return None;
    };
    let k = decode_nat(tc, arg)? as i128;
    match h.kind() {
        ExprKind::Const(nm, _) if nm.to_string() == "Int.ofNat" => Some(k),
        ExprKind::Const(nm, _) if nm.to_string() == "Int.negSucc" => Some(-(k + 1)),
        _ => None,
    }
}

/// Three-valued truth of a CLOSED `Rat.le a b` over the WS-A QUOTIENT `Rat`
/// (`Quot.mk Rat.Raw …`): `Rat.le` δ-reduces through the order bridge to
/// `Int.NonNeg t`, and `t` is a closed `Int` that the kernel's native reducer
/// drives to a numeral. We whnf `Rat.le a b` ONCE, confirm the `Int.NonNeg` head,
/// then decode its argument's SIGN via [`decode_int`] (one further whnf). The
/// quotient `Rat` does NOT reduce to a `Rat.mk num den` normal form (the operands
/// stay as `Quot.mk (Rat.Raw.mk (Int.add (Int.mul …) …) …)`), so we must go
/// through the order bridge rather than decode the rational directly.
///
/// `Some(true)` iff `t ≥ 0`, `Some(false)` iff `t < 0`, `None` if `Rat.le` does
/// not whnf to `Int.NonNeg <numeral>` — the gate never guesses.
fn rat_le_truth(tc: &TypeChecker, a: &Expr, b: &Expr) -> Option<bool> {
    let le = Expr::apps(
        Expr::const_(Name::from_string("Rat.le"), vec![]),
        [a.clone(), b.clone()],
    );
    let w = tc.whnf(&le);
    let ExprKind::App(f, arg) = w.kind() else {
        return None;
    };
    if !matches!(f.kind(), ExprKind::Const(n, _) if n.to_string() == "Int.NonNeg") {
        return None;
    }
    decode_int(tc, arg).map(|v| v >= 0)
}

/// A small exact rational `num/den` (den > 0), the kernel-pinned value of a
/// closed `Rat` quantity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct PinnedRat {
    num: i128,
    den: i128,
}

/// The dyadic denominators that arise for the extremal `BoolFn` witnesses at
/// `n ≤ 3`: every `f̂(S)` for parity/dictator/and/or/const is a dyadic rational
/// `k / 2^m` with `2^m ≤ 2^3 = 8`. We bracket over denominators `{1,2,4,8}` and
/// numerators in `[-den, den]` (each `|f̂(S)| ≤ 1`).
const PIN_DENOMS: &[i128] = &[1, 2, 4, 8];

/// EXACTLY pin the value of a CLOSED `Rat` quantity `e` whose value is a small
/// dyadic rational, using ONLY kernel `Rat.le` decisions: for each candidate
/// `c = num/den` (small dyadic, `|c| ≤ 1`), check `Rat.le e c ∧ Rat.le c e` — both
/// TRUE ⟺ `e = c` on the antisymmetric quotient order. Returns the first match.
///
/// FAITHFULNESS: every comparison is decided by the kernel's `Rat.le` reducer
/// (the order bridge that DOES reduce on the quotient, unlike the raw arithmetic
/// normal form), so the pinned value is exactly the kernel's. `None` if no small
/// dyadic candidate matches (the gate then stays silent on this instance — it
/// never guesses a value).
fn pin_rat_value(tc: &TypeChecker, e: &Expr) -> Option<PinnedRat> {
    for &den in PIN_DENOMS {
        for num in -den..=den {
            let c = signed_rat(num, den as u64);
            let ge = rat_le_truth(tc, &c, e); // c ≤ e
            let le = rat_le_truth(tc, e, &c); // e ≤ c
            if ge == Some(true) && le == Some(true) {
                return Some(PinnedRat { num, den });
            }
        }
    }
    None
}

/// `Rat.mk (Int.ofNat |num|) den` / `Rat.mk (Int.negSucc (|num|-1)) den` — a closed
/// SIGNED rational literal (the kernel's free `Rat.mk` numeral).
fn signed_rat(num: i128, den: u64) -> Expr {
    let int = if num >= 0 {
        Expr::app(
            Expr::const_(Name::from_string("Int.ofNat"), vec![]),
            nat(num as u64),
        )
    } else {
        Expr::app(
            Expr::const_(Name::from_string("Int.negSucc"), vec![]),
            nat((-num - 1) as u64),
        )
    };
    Expr::apps(
        Expr::const_(Name::from_string("Rat.mk"), vec![]),
        [int, nat(den)],
    )
}

/// A CLOSED order proposition normalized to `(carrier, lhs, rhs)` for a `≤`
/// comparison. Recognizes the bare `Rat.le a b` / `Nat.le a b` spellings AND the
/// typeclass `LE.le α inst a b` spelling (the friedgut body uses the latter for
/// its `Rat` comparisons — `LE.le Rat instLERat a b` — and the bare `Nat.le` for
/// the size conjunct).
enum OrderProp {
    Rat(Expr, Expr),
    Nat(Expr, Expr),
}

/// Normalize a CLOSED order prop to [`OrderProp`], or `None` if it is not a `≤`
/// over `Rat`/`Nat` in either spelling.
fn as_order_prop(tc: &TypeChecker, p: &Expr) -> Option<OrderProp> {
    let (head, args) = const_app(p)?;
    match (head.as_str(), args.len()) {
        ("Rat.le", 2) => Some(OrderProp::Rat(args[0].clone(), args[1].clone())),
        ("Nat.le", 2) => Some(OrderProp::Nat(args[0].clone(), args[1].clone())),
        // Typeclass `@LE.le α inst a b` — dispatch on the carrier `α`.
        ("LE.le", 4) => {
            let carrier = tc.whnf(&args[0]);
            let a = args[2].clone();
            let b = args[3].clone();
            if tc.is_def_eq(&carrier, &Expr::const_(Name::from_string("Rat"), vec![])) {
                Some(OrderProp::Rat(a, b))
            } else if tc.is_def_eq(&carrier, &Expr::const_(Name::from_string("Nat"), vec![])) {
                Some(OrderProp::Nat(a, b))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Three-valued truth of a CLOSED proposition `p` the gate can decide:
/// `≤` over `Rat` (via the `Rat.le` order bridge) or `Nat` (decode both operands),
/// in BOTH the bare-constant and the `LE.le` typeclass spelling, AND a conjunction
/// `And p q` of two such (true iff both true — the v2 friedgut body's TWO-SIDED
/// dyadic band guard `2^e·eps ≤ K ∧ K ≤ 2^(e+1)·eps`). `None` for anything else —
/// the gate never guesses.
fn prop_truth(tc: &TypeChecker, p: &Expr) -> Option<bool> {
    // `And lhs rhs` — decide both conjuncts; the conjunction is `Some(true)` iff
    // both are `Some(true)`, `Some(false)` iff some conjunct is decided `false`,
    // and `None` (stay silent) if either conjunct is itself undecidable. The whnf
    // exposes the `And` head when the guard was built as `@And lo hi`.
    let w = tc.whnf(p);
    if let Some((head, args)) = const_app(&w) {
        if head == "And" && args.len() == 2 {
            let lo = prop_truth(tc, &args[0]);
            let hi = prop_truth(tc, &args[1]);
            return match (lo, hi) {
                (Some(true), Some(true)) => Some(true),
                (Some(false), _) | (_, Some(false)) => Some(false),
                _ => None,
            };
        }
    }
    match as_order_prop(tc, p)? {
        OrderProp::Rat(a, b) => rat_le_truth(tc, &a, &b),
        OrderProp::Nat(a, b) => {
            let a = decode_nat(tc, &a)?;
            let b = decode_nat(tc, &b)?;
            Some(a <= b)
        }
    }
}

// ───────────────────────── friedgut-body shape probe ─────────────────────────

/// Outcome of deciding an `∃ J, And(size, mass)` conclusion at a fixed instance.
enum ConclusionVerdict {
    /// SOME enumerated `J` satisfies both `size` and `mass` — conclusion holds.
    Satisfied,
    /// EVERY enumerated `J` (all `2^n` indicators) was decided and NONE satisfied
    /// both conjuncts — conclusion is FALSE at this instance (a refutation).
    AllFail,
    /// At least one `J` / summand did not reduce to a decidable value — undecidable
    /// here, so the gate stays silent (no fabricated refutation).
    Undecided,
}

/// Decide a CLOSED `Exists (HCPoint n) pred` conclusion of the friedgut shape by
/// enumerating every `J : HCPoint n` (the `2^n` mask indicators), instantiating
/// `pred` at `J`, and deciding the resulting `And size mass`:
///
/// - `size = Nat.le (setSizeNat n J) (2^budget)` is kernel-reduced directly
///   (small `Nat`s — cheap, decided by [`prop_truth`]);
/// - `mass = Rat.le (subsetSum n mass_fn) eps` is decided WITHOUT reducing the
///   whole quotient `subsetSum` (which blows up the kernel — see the module note):
///   instead `mass_fn` (the per-`S` summand `ind(notSubsetMask n S J)·f̂(S)²`) is
///   extracted, instantiated at each of the `2^n` indicators `S`, and EACH
///   summand's exact value is kernel-pinned via [`pin_rat_value`] (`Rat.le`
///   brackets reduce on the quotient where the raw sum does not). The summands are
///   added in exact Rust rationals and compared to `eps`.
///
/// FAITHFULNESS: every atom (each `setSizeNat`, each per-`S` summand value, the
/// `eps` bound) comes from the kernel's own reduction; only the FINAL addition of
/// the already-kernel-evaluated summands is done in Rust (the kernel's quotient
/// `Rat.add` does not canonicalize a 4+-term sum without exploding).
fn decode_exists_and(tc: &TypeChecker, n: u64, concl: &Expr) -> ConclusionVerdict {
    let w = tc.whnf(concl);
    let Some((head, args)) = const_app(&w) else {
        return ConclusionVerdict::Undecided;
    };
    // `Exists (HCPoint n) pred` — args = [HCPoint n, pred].
    if head != "Exists" || args.len() != 2 {
        return ConclusionVerdict::Undecided;
    }
    let pred = &args[1];
    // `pred` should be a λ over `J : HCPoint n`.
    let ExprKind::Lam(_, _, pred_body) = pred.kind() else {
        return ConclusionVerdict::Undecided;
    };
    // Guard against an unreasonable enumeration (each indicator costs a kernel
    // reduction; the gate only ever runs at small `n`).
    if n > 6 {
        return ConclusionVerdict::Undecided;
    }
    let total: u64 = 1u64 << n;
    let mut all_decided = true;
    for jmask in 0..total {
        let j = hcpoint_from_mask(n, jmask);
        // `And size mass` after substituting this `J`.
        let inst = tc.whnf(&pred_body.instantiate(&j));
        let Some((h, a)) = const_app(&inst) else {
            all_decided = false;
            continue;
        };
        if h != "And" || a.len() != 2 {
            all_decided = false;
            continue;
        }
        let size_ok = prop_truth(tc, &a[0]);
        let mass_ok = decide_mass_conjunct(tc, n, &a[1]);
        match (size_ok, mass_ok) {
            (Some(true), Some(true)) => return ConclusionVerdict::Satisfied,
            (Some(_), Some(_)) => { /* this J fails; keep scanning */ }
            _ => all_decided = false,
        }
    }
    if all_decided {
        ConclusionVerdict::AllFail
    } else {
        ConclusionVerdict::Undecided
    }
}

/// Decide a friedgut MASS conjunct `Rat.le (subsetSum n mass_fn) eps` by summing
/// the kernel-pinned per-`S` summand values (NOT by reducing the whole quotient
/// sum). Returns `Some(true)` iff `Σ_S value(mass_fn S) ≤ eps`, `Some(false)` iff
/// `>`, `None` if the conjunct is not of the `subsetSum`-`≤`-Rat shape or some
/// summand / `eps` does not kernel-pin.
fn decide_mass_conjunct(tc: &TypeChecker, n: u64, mass_concl: &Expr) -> Option<bool> {
    // `mass_concl = (subsetSum n mass_fn) ≤ eps`  (either `Rat.le` or `LE.le` spelling).
    let OrderProp::Rat(lhs_sum, eps_e) = as_order_prop(tc, mass_concl)? else {
        return None;
    };
    let eps = pin_rat_value(tc, &eps_e)?;
    // LHS must be `subsetSum n mass_fn`.
    let (lh, la) = const_app(&lhs_sum)?;
    if lh != "BoolAnalysis.subsetSum" || la.len() != 2 {
        return None;
    }
    let mass_fn = &la[1];
    let ExprKind::Lam(_, _, summand_body) = mass_fn.kind() else {
        return None;
    };
    if n > 6 {
        return None;
    }
    // Σ_S value(summand_body[S])  in exact rationals.
    let (mut acc_num, mut acc_den): (i128, i128) = (0, 1);
    for smask in 0..(1u64 << n) {
        let s = hcpoint_from_mask(n, smask);
        let term = summand_body.instantiate(&s);
        let v = pin_rat_value(tc, &term)?;
        // acc + v  (exact; denominators are small dyadic so no overflow at n ≤ 6).
        acc_num = acc_num
            .checked_mul(v.den)?
            .checked_add(v.num.checked_mul(acc_den)?)?;
        acc_den = acc_den.checked_mul(v.den)?;
    }
    // acc ≤ eps  ⟺  acc_num·eps_den ≤ eps_num·acc_den.
    let lhs = acc_num.checked_mul(eps.den)?;
    let rhs = eps.num.checked_mul(acc_den)?;
    Some(lhs <= rhs)
}

/// A concrete counterexample witnessing that a friedgut-shaped body is FALSE: at
/// `(n, f, K, eps, e)` every hypothesis holds yet NO admissible junta `J`
/// satisfies the `∃ J, And(size, mass)` conclusion.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {
    /// The cube dimension at which the body fails.
    pub n: u64,
    /// A human-readable label for the refuting Boolean function `f`.
    pub f_label: String,
    /// The influence bound `K` (as `num/denom`).
    pub k: (u64, u64),
    /// The L2 slack `eps` (as `num/denom`).
    pub eps: (u64, u64),
    /// The dyadic exponent `e` (the `∀ e` instantiation that satisfies the guard).
    pub e: u64,
}

impl core::fmt::Display for Counterexample {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let r = |(a, b): (u64, u64)| {
            if b == 1 {
                a.to_string()
            } else {
                format!("{a}/{b}")
            }
        };
        write!(
            fmt,
            "friedgut body FALSE at {{ n = {}, f = {}, K = {}, eps = {}, e = {} }}: \
             hypotheses hold (I[f] ≤ K, 0 ≤ eps, 2^{}·eps ≤ K) but NO junta J with \
             |J| ≤ 2^(BUDGET {}) has masked-mass ≤ eps",
            self.n,
            self.f_label,
            r(self.k),
            r(self.eps),
            self.e,
            self.e,
            self.e,
        )
    }
}

/// The instantiation budget for the small-N refutation search.
#[derive(Clone, Copy, Debug)]
pub struct RefuteBudget {
    /// Maximum cube dimension `n` to sweep (inclusive). 3–4 is plenty: parity at
    /// `n = 2` already refutes the false friedgut body.
    pub max_n: u64,
    /// Maximum dyadic exponent `e` to instantiate the `∀ e` guard with.
    pub max_e: u64,
}

impl Default for RefuteBudget {
    fn default() -> Self {
        // n ≤ 3 sweeps {parity, dictators, and/or, constants} over ≤ 8 indicators;
        // e ≤ 2 covers the small-e conjuncts where the affine BUDGET is tightest.
        Self { max_n: 3, max_e: 2 }
    }
}

/// The `(K, eps)` scalar battery: small positive rationals. Each pair must make
/// the body's `0 ≤ eps` non-vacuity and `I[f] ≤ K` hypotheses satisfiable for at
/// least one witness; the guard `2^e·eps ≤ K` is checked per-instance by the
/// kernel. `eps = 1/2, K = 2` is the design counterexample's pair.
const SCALAR_BATTERY: &[((u64, u64), (u64, u64))] = &[
    ((2, 1), (1, 2)), // K = 2, eps = 1/2  — the friedgut n=2 parity counterexample
    ((1, 1), (1, 2)), // K = 1, eps = 1/2
    ((2, 1), (1, 1)), // K = 2, eps = 1
    ((4, 1), (1, 1)), // K = 4, eps = 1
];

/// Attempt to REFUTE a candidate friedgut-shaped body `body : ∀ n f K eps, Prop`
/// over a small carrier budget. Returns `Some(counterexample)` when an instance
/// makes every hypothesis TRUE while the `∃ J, And(size, mass)` conclusion is
/// FALSE for every admissible junta, and `None` otherwise.
///
/// `body` is the value `Expr` of the helper (the `fun n f K eps => …` lambda).
/// The routine instantiates it at closed `(n, f, K, eps)`, then walks the
/// hypothesis chain (`hI`, `heps`, `∀ e`, guard), discharging each hypothesis ONLY
/// when the kernel decides it TRUE, before decoding the conclusion. A hypothesis
/// the kernel cannot decide (or that is FALSE at the instance) makes the instance
/// vacuous and the search moves on — never a fabricated refutation.
///
/// FAITHFULNESS: the conclusion is decided ENTIRELY by kernel reduction of the
/// closed `subsetSum`/`FourierCoefficient`/`setSizeNat`/`notSubsetMask` terms; no
/// Fourier arithmetic is re-implemented in Rust.
#[must_use]
pub fn refute_friedgut_body(
    tc: &TypeChecker,
    body: &Expr,
    budget: RefuteBudget,
) -> Option<Counterexample> {
    for n in 0..=budget.max_n {
        for w in boolfn_witnesses(n) {
            for &(k, eps) in SCALAR_BATTERY {
                if let Some(cex) = refute_at_instance(tc, body, n, &w, k, eps, budget.max_e) {
                    return Some(cex);
                }
            }
        }
    }
    None
}

/// Try one `(n, f, K, eps)` instance over the dyadic-exponent range `0..=max_e`.
fn refute_at_instance(
    tc: &TypeChecker,
    body: &Expr,
    n: u64,
    w: &BoolFnWitness,
    k: (u64, u64),
    eps: (u64, u64),
    max_e: u64,
) -> Option<Counterexample> {
    // Instantiate `body` at `n, f, K, eps`. `body = fun n f K eps => <chain>`.
    let inst = instantiate_chain(
        tc,
        body,
        &[nat(n), w.func.clone(), rat(k.0, k.1), rat(eps.0, eps.1)],
    )?;
    // `inst` is now `Pi (hI : I[f] ≤ K), Pi (heps : 0 ≤ eps), ∀ e, guard → ∃ J, …`.
    // Walk the two scalar hypotheses, discharging each only if the kernel decides
    // it TRUE.
    let after_hyps = discharge_true_hyps(tc, &inst, 2)?;
    // `after_hyps` is `∀ (e : Nat), guard e → ∃ J, And(size, mass)`.
    let forall_e = tc.whnf(&after_hyps);
    let ExprKind::Pi(_, e_dom, e_body) = forall_e.kind() else {
        return None;
    };
    // Confirm the `∀ e` binder is over `Nat`.
    if !tc.is_def_eq(e_dom, &Expr::const_(Name::from_string("Nat"), vec![])) {
        return None;
    }
    for e in 0..=max_e {
        let with_e = e_body.instantiate(&nat(e));
        // `with_e` = `guard e → ∃ J, …`. Discharge the guard only if TRUE.
        let Some(concl) = discharge_true_hyps(tc, &with_e, 1) else {
            continue;
        };
        match decode_exists_and(tc, n, &concl) {
            ConclusionVerdict::AllFail => {
                return Some(Counterexample {
                    n,
                    f_label: w.label.clone(),
                    k,
                    eps,
                    e,
                })
            }
            ConclusionVerdict::Satisfied | ConclusionVerdict::Undecided => {}
        }
    }
    None
}

/// Instantiate a leading lambda chain `fun a b c … => body` at `args`, returning
/// the substituted body. `None` if `expr` has fewer than `args.len()` leading
/// lambdas (after whnf) — a shape mismatch, not a refutation.
fn instantiate_chain(tc: &TypeChecker, expr: &Expr, args: &[Expr]) -> Option<Expr> {
    let mut cur = expr.clone();
    for a in args {
        let w = tc.whnf(&cur);
        let ExprKind::Lam(_, _, b) = w.kind() else {
            return None;
        };
        cur = b.instantiate(a);
    }
    Some(cur)
}

/// Walk `count` leading non-dependent hypothesis `Pi` binders, discharging each
/// with a sentinel ONLY when the kernel decides its domain prop TRUE. Returns the
/// body after the last discharge, or `None` if any hypothesis is not decided TRUE
/// (a vacuous / undecidable branch — never a refutation).
fn discharge_true_hyps(tc: &TypeChecker, expr: &Expr, count: usize) -> Option<Expr> {
    let mut cur = expr.clone();
    for _ in 0..count {
        let w = tc.whnf(&cur);
        let ExprKind::Pi(_, dom, body) = w.kind() else {
            return None;
        };
        if prop_truth(tc, dom) != Some(true) {
            return None;
        }
        // The proof term is irrelevant to the (closed) conclusion's truth; a
        // sentinel discharges the (necessarily non-dependent) hypothesis binder.
        cur = body.instantiate(&Expr::const_(Name::from_string("True.intro"), vec![]));
    }
    Some(cur)
}

// ──────────────────────────────── gate entry ────────────────────────────────

/// Gate entry: REJECT (return the counterexample) iff the candidate friedgut-shaped
/// `body` is refutable over the default small-N budget, else `Ok`-signal `None`.
///
/// Intended to be called when an opaque axiom of the friedgut shape is redefined to
/// a concrete reducible `Definition` body: a `Some(_)` result means the redefinition
/// installed a FALSE body and must be rejected (fail-closed). A `None` result is
/// NOT a proof of truth — only that no small-N counterexample was found.
#[must_use]
pub fn refute_or_ok(tc: &TypeChecker, body: &Expr) -> Option<Counterexample> {
    refute_friedgut_body(tc, body, RefuteBudget::default())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::env::decl_builder::EnvDeclBuilder;
    use crate::test_utils::run_with_stack;

    /// 256 MB stack — the closed `subsetSum`/`FourierCoefficient`/`chi` ground
    /// reduction is deep enough to overflow the default (and even the 64 MB
    /// `LARGE_STACK`) thread stack; this matches the stack the soundness cert and
    /// the McCormick-attention ground-reduction tests use.
    const REFUTE_STACK: usize = 256 * 1024 * 1024;

    /// Build the env carrying the full Friedgut carrier surface (HCPoint, chi, pm,
    /// ind, FourierCoefficient, subsetSum, notSubsetMask, setSizeNat, …).
    fn friedgut_env() -> Environment {
        let mut env = Environment::new();
        env.init_fourier_boolean()
            .expect("init_fourier_boolean (friedgut carriers)");
        // The body references `notSubsetMask` / `setSizeNat`, registered by the
        // cheap-rungs surface; pull them in explicitly so the reconstructed body
        // type-checks regardless of init order.
        env.register_not_subset_mask()
            .expect("register notSubsetMask + setSizeNat carriers");
        env
    }

    /// Reconstruct the FALSE friedgut L2 body `fun n f K eps => <chain>` via the
    /// still-present `Environment::friedgut_l2_faithful_body` builder.
    fn false_friedgut_body(env: &Environment) -> Expr {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let bool_fn = Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let (k_id, kk) = b.fresh_local(rat.clone());
        let (eps_id, eps) = b.fresh_local(rat.clone());
        let chain = env.friedgut_l2_faithful_body(&b, &n, &f, &kk, &eps);
        let e = b.mk_lam(eps_id, BinderInfo::Default, rat.clone(), chain);
        let e = b.mk_lam(k_id, BinderInfo::Default, rat, e);
        let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat, e);
        b.finish(e)
    }

    /// Reconstruct the v2 body `fun n f K eps => <chain>` via the
    /// `Environment::friedgut_l2_faithful_body_v2` builder (the exponential-budget,
    /// two-sided-band-guard form). NOTE: "faithful" in the builder name is a
    /// MISNOMER — the v2 body fixes the v1 small-n defect but is itself FALSE at
    /// LARGE n (budget `2^(15·2^e) = 2^(7.5·K/eps)` at the low end is below
    /// Friedgut's `2^(12.68·K/eps)` junta; see `gate_blind_to_v2_large_n_falsity`).
    fn v2_body(env: &Environment) -> Expr {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let bool_fn = Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let (k_id, kk) = b.fresh_local(rat.clone());
        let (eps_id, eps) = b.fresh_local(rat.clone());
        let chain = env.friedgut_l2_faithful_body_v2(&b, &n, &f, &kk, &eps);
        let e = b.mk_lam(eps_id, BinderInfo::Default, rat.clone(), chain);
        let e = b.mk_lam(k_id, BinderInfo::Default, rat, e);
        let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat, e);
        b.finish(e)
    }

    /// Reconstruct the v3 body `fun n f K eps => <chain>` via the
    /// `Environment::friedgut_l2_faithful_body_v3` builder (the CORRECTED-BUDGET
    /// `48·2^e` form). This is the body the co-landed `friedgut_boolean`
    /// Axiom→Theorem proof targets. The gate run is the MANDATORY anti-masquerade
    /// rail (necessary, not sufficient — at large gate exponents `2^(48·2^e)` does
    /// not decode to a u64, so the SIZE conjunct is `Undecided`, but the MASS
    /// conjunct against `J = all-coords` is 0 ≤ eps TRUE for every small n, so the
    /// verdict is never `AllFail` — the real faithfulness proof is the kernel-checked
    /// `friedgut_boolean` theorem against this body).
    fn v3_body(env: &Environment) -> Expr {
        let nat = Expr::const_(Name::from_string("Nat"), vec![]);
        let rat = Expr::const_(Name::from_string("Rat"), vec![]);
        let bool_fn = Expr::const_(Name::from_string("BoolAnalysis.BoolFn"), vec![]);
        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let bool_fn_n = Expr::app(bool_fn.clone(), n.clone());
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let (k_id, kk) = b.fresh_local(rat.clone());
        let (eps_id, eps) = b.fresh_local(rat.clone());
        let chain = env.friedgut_l2_faithful_body_v3(&b, &n, &f, &kk, &eps);
        let e = b.mk_lam(eps_id, BinderInfo::Default, rat.clone(), chain);
        let e = b.mk_lam(k_id, BinderInfo::Default, rat, e);
        let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat, e);
        b.finish(e)
    }

    /// STRUCTURAL-BLINDNESS DEMONSTRATION (the hard lesson of this campaign): the
    /// small-n gate returns `None` on the v2 body over the full default sweep
    /// (n ≤ 3 × {parity, dictators, and/or, constants} × the 4 (K,eps) pairs × e ≤ 2)
    /// — yet the v2 body is **FALSE at large n**. At every small `n` the full set
    /// `J := (fun _ => true)` trivially satisfies the conclusion (`|J| = n ≤ budget`,
    /// masked-mass `= 0`), so the gate CANNOT reach the regime (n ≈ 2^(K/eps)) where
    /// the budget `2^(15·2^e) = 2^(7.5·K/eps)` falls below Friedgut's `2^(12.68·K/eps)`
    /// junta and the body fails. The `None` is a GENUINE examination (not a parse-miss
    /// — the two-sided `And(le,le)` guard is decided, and `v2_budget_decodes_at_gate_exponents`
    /// pins the `2^60` size bound is concretely decodable), and the companion
    /// `refutes_friedgut_false_body_at_n2_parity` shows the SAME gate DOES refute the
    /// v1 small-n falsity — so this `None` is discriminating, not a silent always-`None`.
    /// CONCLUSION: "gate-passes" is necessary but NOT sufficient for an `n`-scaling
    /// junta-size claim; the helper therefore stays an opaque Axiom (TCB 5), and only
    /// a genuine Axiom→Theorem proof retires friedgut. This test PINS that blindness so
    /// nobody re-reads a v2 `None` as a faithfulness certificate again.
    #[test]
    fn gate_blind_to_v2_large_n_falsity() {
        run_with_stack(REFUTE_STACK, || {
            let env = friedgut_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            let body = v2_body(&env);
            assert_eq!(
                refute_or_ok(&tc, &body),
                None,
                "the small-n gate returns None on the v2 body (J=full passes for all \
                 small n) — DESPITE the v2 body being false at large n. This None is a \
                 blindness demonstration, NOT a faithfulness certificate: it must not be \
                 used to justify installing the v2 body as friedgut_boolean_helper's value."
            );
        });
    }

    /// MANDATORY anti-masquerade rail for the v3 (CORRECTED-budget `48·2^e`) body:
    /// `refute_or_ok` must return `None` over the default small-N sweep. This is
    /// NECESSARY (a `Some(_)` would mean the v3 body is small-n refutable and the
    /// `friedgut_boolean` proof against it would be impossible) but NOT SUFFICIENT
    /// (the gate is structurally blind to large-n junta-size claims — see
    /// `gate_blind_to_v2_large_n_falsity`). The REAL faithfulness check is that the
    /// co-landed `friedgut_boolean` Axiom→Theorem proof kernel-checks against this
    /// exact body. With `c = 48` the size budget at e≥1 (`2^192`) no longer decodes
    /// to a u64, so the SIZE conjunct is `Undecided`; the MASS conjunct against
    /// `J = all-coords` is `0 ≤ eps` (TRUE) for every small n, so the verdict is
    /// never `AllFail` and the gate stays silent.
    #[test]
    fn gate_passes_v3_corrected_body() {
        run_with_stack(REFUTE_STACK, || {
            let env = friedgut_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            let body = v3_body(&env);
            assert_eq!(
                refute_or_ok(&tc, &body),
                None,
                "the small-n gate must return None on the v3 (48·2^e) body — the \
                 mandatory necessary anti-masquerade rail before any friedgut_boolean \
                 proof lands against this body."
            );
        });
    }

    /// NON-VACUITY of the v2 `None`: the gate's `None` on the v2 body must be a
    /// GENUINE examination (it found `J = all-coords` SATISFIES the conclusion at
    /// the pinned `e`), NOT a silent `Undecided` from a budget too large to decode.
    /// The v2 budget `2^(15·2^e)` at the largest gate exponent `e = 2` is `2^60`,
    /// which MUST kernel-decode to a concrete `u64` `Nat` (it is `< 2^63`); if it
    /// did not, the size conjunct would be `Undecided` and the `None` would be
    /// vacuous. This pins that the size conjunct is decidable (so the gate examines
    /// the v2 conclusion), keeping `gate_blind_to_v2_large_n_falsity` meaningful (the
    /// gate genuinely examined and found J=full satisfying — it just cannot reach the
    /// large-n regime where the v2 body actually fails).
    #[test]
    fn v2_budget_decodes_at_gate_exponents() {
        run_with_stack(REFUTE_STACK, || {
            let env = friedgut_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            // BUDGET2 e = 15·2^e, so `Nat.pow 2 (15·2^e)` is the junta-size bound.
            for e in 0u64..=2 {
                let budget_exp = env.friedgut_budget_v2(&nat(e));
                let size_bound = Expr::apps(
                    Expr::const_(Name::from_string("Nat.pow"), vec![]),
                    [nat(2), budget_exp],
                );
                let decoded = decode_nat(&tc, &size_bound).unwrap_or_else(|| {
                    panic!("v2 budget 2^(15·2^{e}) must kernel-decode to a concrete Nat")
                });
                assert_eq!(
                    decoded,
                    1u64 << (15 * (1u64 << e)),
                    "v2 budget at e={e} must be exactly 2^(15·2^{e})"
                );
            }
        });
    }

    /// THE ACCEPTANCE BAR. The refutation routine must FIND the counterexample to
    /// the reconstructed friedgut FALSE body, and it must be exactly the design
    /// counterexample: `n = 2`, `f = parity(χ_{[2]})`, `K = 2`, `eps = 1/2`,
    /// `e = 0` — every junta with `|J| ≤ 2^(BUDGET 0) = 2^0 = 1` has masked-mass
    /// `= 1 > 1/2`, so NO 1-junta works ⇒ the body is FALSE.
    ///
    /// This is the decisive test: if the kernel-reduction-of-instances approach
    /// works, the routine refutes the false body here. Runs on a LARGE_STACK
    /// thread because the closed `subsetSum`/`FourierCoefficient`/`chi` reduction
    /// is deep (otherwise the kernel `whnf` SIGBUS-overflows the default stack —
    /// the same gotcha the foundation ground-reduction tests handle).
    #[test]
    fn refutes_friedgut_false_body_at_n2_parity() {
        run_with_stack(REFUTE_STACK, || {
            let env = friedgut_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            let body = false_friedgut_body(&env);

            let cex = refute_friedgut_body(&tc, &body, RefuteBudget::default())
                .expect("the routine MUST refute the FALSE friedgut body");

            assert_eq!(cex.n, 2, "the counterexample must be at n = 2");
            assert!(
                cex.f_label.starts_with("parity"),
                "the refuting f must be parity (the spread-out extremal): {}",
                cex.f_label
            );
            assert_eq!(cex.k, (2, 1), "K must be 2");
            assert_eq!(cex.eps, (1, 2), "eps must be 1/2");
            assert_eq!(cex.e, 0, "the refuting dyadic exponent must be e = 0");
        });
    }

    /// `refute_or_ok` (the GATE entry) must REJECT the false friedgut body.
    #[test]
    fn gate_rejects_false_friedgut_body() {
        run_with_stack(REFUTE_STACK, || {
            let env = friedgut_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            let body = false_friedgut_body(&env);
            assert!(
                refute_or_ok(&tc, &body).is_some(),
                "the gate must fail-closed (reject) on the false friedgut body"
            );
        });
    }

    /// NO-FALSE-POSITIVE check. A TRIVIALLY-TRUE friedgut-shaped body — same shape
    /// but with a HUGE `eps` slack on the mass conjunct (and the same generous
    /// size budget) — must NOT be refuted: for every instance the empty junta
    /// `J = ∅` already satisfies `|∅| = 0 ≤ 2^(BUDGET e)` and masked-mass `≤ eps`
    /// (the mass is at most `E[f̃²] = 1 ≤ 100`), so the conclusion holds. The gate
    /// must stay SILENT (sound — no false alarm). A small budget keeps the sweep
    /// fast while still covering the design `(n=2, parity, e=0)` instance that
    /// refutes the FALSE body — proving the bound (not the shape) is what matters.
    #[test]
    fn does_not_refute_trivially_true_body() {
        run_with_stack(REFUTE_STACK, || {
            let env = friedgut_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            let body = trivially_true_body(&env);
            // Budget capped at n ≤ 2 so the sweep stays fast; it STILL includes the
            // exact (n=2, parity, e=0) instance that refutes the false body — so a
            // `None` here is a genuine no-false-positive result on that instance.
            let budget = RefuteBudget { max_n: 2, max_e: 2 };
            assert_eq!(
                refute_friedgut_body(&tc, &body, budget),
                None,
                "the routine must NOT refute a trivially-true body (no false positive)"
            );
        });
    }

    /// A trivially-TRUE friedgut-shaped body: identical hypothesis chain and
    /// `∃ J, And(size, mass)` conclusion, but the mass bound is `eps + 100` (a
    /// huge slack) and the size budget is `2^(BUDGET e)` as before — so the empty
    /// junta always satisfies both conjuncts. Built directly (not via the false
    /// builder) so the only difference from the false body is the loosened mass
    /// bound. The mass term and all carriers are the SAME (real `subsetSum` /
    /// `FourierCoefficient` / `notSubsetMask` / `setSizeNat`), so this exercises
    /// the SAME kernel-reduction path — only the bound differs.
    fn trivially_true_body(_env: &Environment) -> Expr {
        let cc = |s: &str| Expr::const_(Name::from_string(s), vec![]);
        let nat = cc("Nat");
        let rat = cc("Rat");
        let nat_succ = cc("Nat.succ");
        let nat_zero = cc("Nat.zero");
        let int_of_nat = cc("Int.ofNat");
        let rat_mk = cc("Rat.mk");
        let rat_mul = cc("Rat.mul");
        let rat_add = cc("Rat.add");
        let rat_zero = cc("Rat.zero");
        let nat_pow = cc("Nat.pow");
        let nat_le = cc("Nat.le");
        let rat_le = cc("Rat.le");
        let hcpoint = cc("BoolAnalysis.HCPoint");
        let subset_sum = cc("BoolAnalysis.subsetSum");
        let ind = cc("BoolAnalysis.ind");
        let not_subset_mask = cc("BoolAnalysis.notSubsetMask");
        let set_size_nat = cc("BoolAnalysis.setSizeNat");
        let fourier = cc("BoolAnalysis.FourierCoefficient");
        let total_influence = cc("BoolAnalysis.TotalInfluence");
        let u1 = crate::level::Level::succ(crate::level::Level::zero());

        let one_nat = Expr::app(nat_succ.clone(), nat_zero.clone());
        let two_nat = Expr::app(nat_succ.clone(), one_nat.clone());
        let mul = |a: Expr, b: Expr| Expr::apps(rat_mul.clone(), [a, b]);
        let le = |a: Expr, b: Expr| Expr::apps(rat_le.clone(), [a, b]);
        let natcast = |m: Expr| {
            Expr::apps(
                rat_mk.clone(),
                [Expr::app(int_of_nat.clone(), m), one_nat.clone()],
            )
        };
        // `100/1`.
        let hundred = {
            let mut k = nat_zero.clone();
            for _ in 0..100 {
                k = Expr::app(nat_succ.clone(), k);
            }
            Expr::apps(
                rat_mk.clone(),
                [Expr::app(int_of_nat.clone(), k), one_nat.clone()],
            )
        };

        let mut b = EnvDeclBuilder::new();
        let (n_id, n) = b.fresh_local(nat.clone());
        let bool_fn_n = Expr::app(cc("BoolAnalysis.BoolFn"), n.clone());
        let (f_id, f) = b.fresh_local(bool_fn_n.clone());
        let (k_id, kk) = b.fresh_local(rat.clone());
        let (eps_id, eps) = b.fresh_local(rat.clone());

        let hcpoint_n = Expr::app(hcpoint.clone(), n.clone());
        let ti = Expr::apps(total_influence.clone(), [n.clone(), f.clone()]);

        // hI : I[f] ≤ K ; heps : 0 ≤ eps.
        let hi_ty = le(ti, kk.clone());
        let (hi_id, _) = b.fresh_local(hi_ty.clone());
        let heps_ty = le(rat_zero.clone(), eps.clone());
        let (heps_id, _) = b.fresh_local(heps_ty.clone());

        let dyadic = {
            let mut d = EnvDeclBuilder::child_of(&b);
            let (e_id, e) = d.fresh_local(nat.clone());
            let pow2e = Expr::apps(nat_pow.clone(), [two_nat.clone(), e.clone()]);
            let guard_ty = le(mul(natcast(pow2e), eps.clone()), kk.clone());
            let (guard_id, _) = d.fresh_local(guard_ty.clone());

            let pred = {
                let mut g = EnvDeclBuilder::child_of(&d);
                let (j_id, j) = g.fresh_local(hcpoint_n.clone());
                let size_j = Expr::apps(set_size_nat.clone(), [n.clone(), j.clone()]);
                // BUDGET e := e + e.
                let budget = Expr::apps(cc("Nat.add"), [e.clone(), e.clone()]);
                let pow2b = Expr::apps(nat_pow.clone(), [two_nat.clone(), budget]);
                let size_concl = Expr::apps(nat_le.clone(), [size_j, pow2b]);
                let mass_fn = {
                    let mut h = EnvDeclBuilder::child_of(&g);
                    let (s_id, s) = h.fresh_local(hcpoint_n.clone());
                    let coeff = Expr::apps(fourier.clone(), [n.clone(), f.clone(), s.clone()]);
                    let sq = mul(coeff.clone(), coeff);
                    let mask =
                        Expr::apps(not_subset_mask.clone(), [n.clone(), s.clone(), j.clone()]);
                    let body = mul(Expr::app(ind.clone(), mask), sq);
                    h.finish_child(h.mk_lam(s_id, BinderInfo::Default, hcpoint_n.clone(), body))
                };
                let mass = Expr::apps(subset_sum.clone(), [n.clone(), mass_fn]);
                // mass ≤ eps + 100  (the HUGE slack — always satisfiable by J = ∅).
                let mass_concl = le(mass, Expr::apps(rat_add.clone(), [eps.clone(), hundred]));
                let and = Expr::apps(cc("And"), [size_concl, mass_concl]);
                g.finish_child(g.mk_lam(j_id, BinderInfo::Default, hcpoint_n.clone(), and))
            };
            let exists = Expr::apps(
                Expr::const_(Name::from_string("Exists"), vec![u1.clone()]),
                [hcpoint_n.clone(), pred],
            );
            let body = d.mk_pi(guard_id, BinderInfo::Default, guard_ty, exists);
            d.finish_child(d.mk_pi(e_id, BinderInfo::Default, nat.clone(), body))
        };

        let e = b.mk_pi(heps_id, BinderInfo::Default, heps_ty, dyadic);
        let chain = b.mk_pi(hi_id, BinderInfo::Default, hi_ty, e);
        let e = b.mk_lam(eps_id, BinderInfo::Default, rat.clone(), chain);
        let e = b.mk_lam(k_id, BinderInfo::Default, rat, e);
        let e = b.mk_lam(f_id, BinderInfo::Default, bool_fn_n, e);
        let e = b.mk_lam(n_id, BinderInfo::Default, nat, e);
        b.finish(e)
    }

    /// Sanity: the `hcpoint_from_mask` indicator reads back its bits under kernel
    /// reduction — `point ⟨v⟩` is `Bool.true` iff bit `v` is set. Pins that the
    /// junta-enumeration witnesses are the genuine `2^n` indicators.
    #[test]
    fn hcpoint_mask_reads_back_its_bits() {
        run_with_stack(REFUTE_STACK, || {
            let env = friedgut_env();
            let tc = TypeChecker::with_mode(&env, env.mode());
            // n = 2, mask = 0b10 (only coordinate 1 set).
            let point = hcpoint_from_mask(2, 0b10);
            let at0 = tc.whnf(&Expr::app(point.clone(), fin_mk(2, 0)));
            let at1 = tc.whnf(&Expr::app(point, fin_mk(2, 1)));
            assert!(
                tc.is_def_eq(&at0, &Expr::const_(Name::from_string("Bool.false"), vec![])),
                "mask 0b10 at coord 0 must be false"
            );
            assert!(
                tc.is_def_eq(&at1, &Expr::const_(Name::from_string("Bool.true"), vec![])),
                "mask 0b10 at coord 1 must be true"
            );
        });
    }
}
