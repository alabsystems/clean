// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Prop-level literal comparison simprocs: Lean 4.8's `Nat.reduceLT`,
//! `Nat.reduceGT` and (for `≤`/`≥` between numerals) `Nat.reduceLeDiff`, and
//! `Int.reduceLT` / `reduceGT` / `reduceLE` / `reduceGE` (G41, ledger (111)).
//!
//! Numerals are arbitrary-precision (`BigNat`), as Lean's are: a comparison
//! at or above `2^64` decides like any other. A numeral is read only at its
//! canonical instance (`instOfNatNat n`, Lean's `instOfNat` / `Int.instOfNat`
//! for `Int`): `instance : OfNat Nat 5 := ⟨7⟩` makes `(5 : Nat)` a numeral
//! this reducer does not read.
//!
//! Lean's builtin simp set rewrites a comparison of two numerals to `True` or
//! `False` (`reduceBinPred` → `evalPropStep`), so `(1024 : Nat) > 0` closes
//! under a bare `simp` and `(0 : Nat) > 1024` becomes `False`. Clean's table
//! (`simproc_builtins::register_nat_comparisons`) only evaluated the `Bool`
//! heads `Nat.blt` / `Nat.ble`, so the `Prop` heads reported "no progress".
//!
//! Every rewrite carries a REAL proof of `p = True` / `p = False`, never
//! `proof: None` (a Prop is not definitionally `True`), and every proof is
//! constant-size in the literals:
//!
//! * `Nat` — `nat_le_bridge::nat_le_lits` (`Nat.le_of_ble_eq_true` over an
//!   `Eq.refl true` the kernel settles by one GMP-backed `Nat.ble` fold) for a
//!   true comparison, and `nat_le_bridge::nat_false_of_lits_le` under a
//!   `fun h : p => …` for a false one. `a < b` is `Nat.le (a+1) b`.
//! * `Int` — Lean's own spelling, `of_decide_eq_true` / `of_decide_eq_false`
//!   over `Int.decLt` / `Int.decLe`, which reduce through `Nat` arithmetic on
//!   the literals rather than in unary.
//!
//! Both are wrapped by `prop_true_proof` / `prop_false_proof` (Lean's
//! `eq_true` / `eq_false`, spelled from prelude constants). The kernel re-check
//! at `close_goal` is what decides: a wrong verdict here cannot close a goal.

use std::cmp::Ordering;

use clean_kernel::expr::{ExprKind, Literal};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{BigNat, BinderInfo, Expr};

use crate::tactic::core::ProofState;
use crate::tactic::nat_le_bridge::{nat_false_of_lits_le_big, nat_le_lits_big};

use super::lemmas::{prop_false_proof, prop_true_proof};
use super::types::SimpResult;

/// The four comparison heads, each a `(α, inst, a, b)` application.
const HEADS: &[(&str, Cmp)] = &[
    ("LT.lt", Cmp::Lt),
    ("GT.gt", Cmp::Gt),
    ("LE.le", Cmp::Le),
    ("GE.ge", Cmp::Ge),
];

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Cmp {
    Lt,
    Gt,
    Le,
    Ge,
}

impl Cmp {
    /// `(strict, swapped)`: `a > b` is `b < a`, `a ≥ b` is `b ≤ a`.
    fn normalize(self) -> (bool, bool) {
        match self {
            Cmp::Lt => (true, false),
            Cmp::Gt => (true, true),
            Cmp::Le => (false, false),
            Cmp::Ge => (false, true),
        }
    }

    /// This comparison's bit in a [`LiteralCmps`] set, for type `ty`.
    fn bit(self, ty: &str) -> Option<u8> {
        let base = match ty {
            "Nat" => 0,
            "Int" => 4,
            _ => return None,
        };
        let offset = match self {
            Cmp::Lt => 0,
            Cmp::Gt => 1,
            Cmp::Le => 2,
            Cmp::Ge => 3,
        };
        Some(1 << (base + offset))
    }
}

/// Which `(type, comparison)` pairs a simp call decides: one bit per pair.
pub(crate) type LiteralCmps = u8;

/// Every pair: Lean's default simp set (`Nat.reduceLeDiff` covers `≤`/`≥`).
pub(crate) const ALL_LITERAL_CMPS: LiteralCmps = u8::MAX;

/// The pair a Lean 4.8.0 comparison simproc named in a `simp only` list
/// decides, or `None` for a name that is not one Clean implements.
/// `Nat.reduceLeDiff` is not here: it also cancels common offsets (`x + 2 ≤
/// x + 5`), which this reducer does not, so it stays refused by name.
pub(crate) fn literal_cmp_simproc(name: &Name) -> Option<LiteralCmps> {
    let (ty, cmp) = match name.to_string().as_str() {
        "Nat.reduceLT" => ("Nat", Cmp::Lt),
        "Nat.reduceGT" => ("Nat", Cmp::Gt),
        "Int.reduceLT" => ("Int", Cmp::Lt),
        "Int.reduceGT" => ("Int", Cmp::Gt),
        "Int.reduceLE" => ("Int", Cmp::Le),
        "Int.reduceGE" => ("Int", Cmp::Ge),
        _ => return None,
    };
    cmp.bit(ty)
}

fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn const_name(e: &Expr) -> Option<String> {
    match e.kind() {
        ExprKind::Const(name, _) => Some(name.to_string()),
        _ => None,
    }
}

fn raw_nat_lit(e: &Expr) -> Option<&BigNat> {
    match e.kind() {
        ExprKind::Lit(Literal::Nat(n)) => Some(n),
        _ => None,
    }
}

/// `inst` is `<one of heads> <lit>` with the literal `lit` itself.
fn instance_of_literal(inst: &Expr, heads: &[&str], lit: &BigNat) -> bool {
    let args = inst.get_app_args();
    const_name(inst.get_app_fn()).is_some_and(|h| heads.contains(&h.as_str()))
        && matches!(args.as_slice(), [n] if raw_nat_lit(n).is_some_and(|m| m.cmp(lit) == Ordering::Equal))
}

/// A raw `Nat` literal, or `@OfNat.ofNat Nat <lit> (instOfNatNat <lit>)` —
/// Lean's `Nat.fromExpr?` shapes at the canonical instance.
fn nat_numeral(e: &Expr) -> Option<BigNat> {
    if let Some(n) = raw_nat_lit(e) {
        return Some(n.clone());
    }
    let args = e.get_app_args();
    match (const_name(e.get_app_fn()).as_deref(), args.as_slice()) {
        (Some("OfNat.ofNat"), [ty, lit, inst]) if const_name(ty).as_deref() == Some("Nat") => {
            let n = raw_nat_lit(lit)?;
            instance_of_literal(inst, &["instOfNatNat"], n).then(|| n.clone())
        }
        _ => None,
    }
}

/// An `Int` numeral: its sign and magnitude (`neg` only for a non-zero
/// magnitude).
#[derive(Debug, Clone, PartialEq, Eq)]
struct IntLit {
    neg: bool,
    mag: BigNat,
}

impl IntLit {
    fn new(neg: bool, mag: BigNat) -> Self {
        let neg = neg && !mag.is_zero();
        IntLit { neg, mag }
    }

    fn cmp(&self, other: &Self) -> Ordering {
        match (self.neg, other.neg) {
            (false, false) => self.mag.cmp(&other.mag),
            (true, true) => other.mag.cmp(&self.mag),
            (true, false) => Ordering::Less,
            (false, true) => Ordering::Greater,
        }
    }

    #[cfg(test)]
    fn to_i128(&self) -> Option<i128> {
        let m = i128::from(self.mag.to_u64()?);
        Some(if self.neg { -m } else { m })
    }
}

/// An `Int` numeral — `Int.ofNat <nat numeral>`, `@OfNat.ofNat Int <lit>
/// (instOfNat <lit>)`, `Int.negSucc <nat numeral>` or `-<one of those>` —
/// Lean's `Int.fromExpr?`.
fn int_numeral(e: &Expr) -> Option<IntLit> {
    let args = e.get_app_args();
    match (const_name(e.get_app_fn()).as_deref(), args.as_slice()) {
        (Some("Int.ofNat"), [n]) => nat_numeral(n).map(|n| IntLit::new(false, n)),
        (Some("Int.negSucc"), [n]) => {
            nat_numeral(n).map(|n| IntLit::new(true, n.checked_add_big(&BigNat::from(1))))
        }
        (Some("OfNat.ofNat"), [ty, lit, inst]) if const_name(ty).as_deref() == Some("Int") => {
            let n = raw_nat_lit(lit)?;
            instance_of_literal(inst, &["instOfNat", "Int.instOfNat"], n)
                .then(|| IntLit::new(false, n.clone()))
        }
        (Some("Neg.neg"), [ty, inst, x]) if const_name(ty).as_deref() == Some("Int") => {
            if !matches!(
                const_name(inst).as_deref(),
                Some("instNegInt" | "Int.instNegInt")
            ) {
                return None;
            }
            // `-(-k)` is not a numeral in Lean's reading; only negate a
            // non-negated literal.
            if const_name(x.get_app_fn()).as_deref() == Some("Neg.neg") {
                return None;
            }
            int_numeral(x).map(|v| IntLit::new(!v.neg, v.mag))
        }
        _ => None,
    }
}

/// The canonical `LT`/`LE` instance names of `Nat` and `Int`, in Clean's
/// builtin prelude and in Lean's `Init`.
fn canonical_instance(ty: &str, strict: bool, inst: &Expr) -> bool {
    let Some(name) = const_name(inst) else {
        return false;
    };
    match (ty, strict) {
        ("Nat", true) => name == "instLTNat",
        ("Nat", false) => name == "instLENat",
        ("Int", true) => name == "instLTInt" || name == "Int.instLTInt",
        ("Int", false) => name == "instLEInt" || name == "Int.instLEInt",
        _ => false,
    }
}

/// Lean's literal comparison simprocs on `expr`: the `True`/`False` it
/// decides, with a proof of `expr = True` / `expr = False`, when `expr`'s
/// `(type, comparison)` is in `allowed`.
///
/// Lean 4.8's `simp only` starts from an EMPTY simproc set
/// (`Lean/Elab/Tactic/Simp.lean`, `mkSimpContext`), and pinned 4.8.0 reports
/// "simp made no progress" for `(1024 : Nat) > 0 := by simp only []`; the
/// caller passes the pairs the call's simprocs decide
/// (`SimprocScope::literal_cmps`).
///
/// ENSURES: `Some` only for a `Nat` or `Int` comparison of two numerals at the
///   canonical instances, whose pair is in `allowed`.
pub(crate) fn reduce_literal_cmp(
    state: &ProofState,
    expr: &Expr,
    allowed: LiteralCmps,
) -> Option<SimpResult> {
    let head = const_name(expr.get_app_fn())?;
    let cmp = HEADS
        .iter()
        .find(|(name, _)| *name == head)
        .map(|(_, c)| *c)?;
    let args = expr.get_app_args();
    let [ty, inst, a, b] = args.as_slice() else {
        return None;
    };
    let ty_name = const_name(ty)?;
    if cmp.bit(&ty_name)? & allowed == 0 {
        return None;
    }
    let (strict, swapped) = cmp.normalize();
    let (lo, hi) = if swapped { (*b, *a) } else { (*a, *b) };
    if !canonical_instance(&ty_name, strict, inst) {
        return None;
    }
    match ty_name.as_str() {
        "Nat" => nat_outcome(expr, strict, lo, hi),
        "Int" => int_outcome(state, expr, strict, lo, hi),
        _ => None,
    }
}

/// `p := lo < hi` (strict) or `lo ≤ hi` over `Nat` numerals.
fn nat_outcome(p: &Expr, strict: bool, lo: &Expr, hi: &Expr) -> Option<SimpResult> {
    let lo = nat_numeral(lo)?;
    let hi = nat_numeral(hi)?;
    // `lo < hi` is `Nat.le (lo + 1) hi` by `Nat.lt`'s definition.
    let left = if strict {
        lo.checked_add_big(&BigNat::from(1))
    } else {
        lo
    };
    if left <= hi {
        return Some(SimpResult {
            expr: konst("True"),
            proof: Some(prop_true_proof(p, &nat_le_lits_big(&left, &hi))),
        });
    }
    // `fun h : p => False`, with `h : Nat.le left hi` and `left > hi`.
    let refute = nat_false_of_lits_le_big(Expr::bvar(0), &left, &hi)?;
    let not_p = Expr::lam(BinderInfo::Default, p.clone(), refute);
    Some(SimpResult {
        expr: konst("False"),
        proof: Some(prop_false_proof(p, &not_p)),
    })
}

/// `p := lo < hi` (strict) or `lo ≤ hi` over `Int` numerals, by Lean's
/// `of_decide_eq_true` / `of_decide_eq_false` over `Int.decLt` / `Int.decLe`.
fn int_outcome(
    state: &ProofState,
    p: &Expr,
    strict: bool,
    lo_e: &Expr,
    hi_e: &Expr,
) -> Option<SimpResult> {
    let lo = int_numeral(lo_e)?;
    let hi = int_numeral(hi_e)?;
    let dec_name = if strict { "Int.decLt" } else { "Int.decLe" };
    for needed in [dec_name, "of_decide_eq_true", "of_decide_eq_false"] {
        state.env.get_const(&Name::from_string(needed))?;
    }
    let order = lo.cmp(&hi);
    let holds = if strict {
        order == Ordering::Less
    } else {
        order != Ordering::Greater
    };
    let inst = Expr::apps(konst(dec_name), [lo_e.clone(), hi_e.clone()]);
    let refl = |value: &str| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq.refl"),
                vec![Level::succ(Level::zero())],
            ),
            [konst("Bool"), konst(value)],
        )
    };
    if holds {
        let h = Expr::apps(
            konst("of_decide_eq_true"),
            [p.clone(), inst, refl("Bool.true")],
        );
        return Some(SimpResult {
            expr: konst("True"),
            proof: Some(prop_true_proof(p, &h)),
        });
    }
    let not_p = Expr::apps(
        konst("of_decide_eq_false"),
        [p.clone(), inst, refl("Bool.false")],
    );
    Some(SimpResult {
        expr: konst("False"),
        proof: Some(prop_false_proof(p, &not_p)),
    })
}

#[cfg(test)]
#[path = "simproc_builtins_cmp_tests.rs"]
mod tests;
