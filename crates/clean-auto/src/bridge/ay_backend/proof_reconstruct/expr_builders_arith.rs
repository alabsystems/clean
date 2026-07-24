// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Arithmetic ordering proof builders for proof reconstruction.
//!
//! Builds kernel Expr terms for transitivity/monotonicity lemmas used by LRA
//! Farkas proof reconstruction. Supports all four combinations of `≤` and `<`:
//! - `≤` + `≤` → `le_trans`
//! - `≤` + `<` → `lt_of_le_of_lt`
//! - `<` + `≤` → `lt_of_lt_of_le`
//! - `<` + `<` → `lt_trans`

use ay::Sort;
use clean_kernel::name::Name;
use clean_kernel::{BinderInfo, Expr, ExprKind, Level};

use crate::arith_proof::ArithSort;
pub(crate) use crate::bridge::arith_chain::{combine_ops, CmpOp};
use crate::bridge::rat_smt::detect_rat_arith_sort;

/// Convert a ay `Sort` to the shared `ArithSort` for chain-step delegation.
fn ay_sort_to_arith(sort: &Sort) -> Option<ArithSort> {
    if sort.is_int() || sort.is_real() {
        Some(detect_rat_arith_sort(sort, None))
    } else {
        None
    }
}

/// Build one chain step for any supported sort, dispatching on sort + op.
///
/// Delegates to the shared `arith_proof::mk_chain_step` (#2910).
/// Returns `None` for non-arithmetic sorts so the caller falls back to trust.
pub(crate) fn mk_chain_step_for_sort(
    sort: &Sort,
    a: &Expr,
    b: &Expr,
    c: &Expr,
    left_op: CmpOp,
    right_op: CmpOp,
    h1: &Expr,
    h2: &Expr,
) -> Option<Expr> {
    let arith = ay_sort_to_arith(sort)?;
    Some(crate::arith_proof::mk_chain_step(
        arith, a, b, c, left_op, right_op, h1, h2,
    ))
}

/// Build a kernel-verified `False` proof from a cyclic chain using `lt_irrefl`.
///
/// Given `chain_proof : a < a` (from a cyclic transitivity chain), applies
/// `@Sort.lt_irrefl a chain_proof : False`. This eliminates the need for
/// `trustedArith` in the closing step of cyclic Farkas chains.
///
/// Only works when the chain's combined op is `Lt` (at least one strict bound
/// in the cycle). Returns `None` for unsupported sorts or `Le` chains.
///
/// Delegates to the shared `arith_proof::mk_lt_irrefl_false` (#2910).
pub(crate) fn mk_lt_irrefl_false(sort: &Sort, a: &Expr, chain_proof: &Expr) -> Option<Expr> {
    let arith = ay_sort_to_arith(sort)?;
    Some(crate::arith_proof::mk_lt_irrefl_false(
        arith,
        a,
        chain_proof,
    ))
}

/// Build a kernel-verified `False` proof for a contradictory Int bound with
/// concrete endpoints using `NonNeg.casesOn`.
///
/// When a chain proves `a ≤ c` (or `a < c`) for concrete Int values where
/// the bound is violated, the chain proof's type reduces to
/// `Int.NonNeg (Int.negSucc k)`. This uses `NonNeg.casesOn` with an
/// `Int.casesOn` discriminating motive:
///
/// ```text
/// @Int.NonNeg.casesOn
///   (fun (x : Int) (_ : NonNeg x) =>
///     @Int.casesOn.{1} (fun _ => Prop) x (fun _ => True) (fun _ => False))
///   nonneg_index  chain_proof
///   (fun (n : Nat) => True.intro)
/// ```
///
/// The motive maps `ofNat` indices to `True` (constructor case is trivial)
/// and `negSucc` indices to `False` (the actual result). The kernel's iota
/// rule reduces `Int.casesOn ... (negSucc k) ...` to `False`.
pub(crate) fn mk_int_concrete_false(
    op: CmpOp,
    start: &Expr,
    end_: &Expr,
    chain_proof: &Expr,
) -> Expr {
    // Compute the NonNeg index matching the chain proof's reduced type.
    // For Le: Int.le start end_ = NonNeg (Int.sub end_ start)
    // For Lt: Int.lt start end_ = Int.le (add start 1) end_
    //       = NonNeg (Int.sub end_ (Int.add start (ofNat 1)))
    let int_sub = Expr::const_(Name::from_string("Int.sub"), vec![]);
    let nonneg_index = match op {
        CmpOp::Le => Expr::app(Expr::app(int_sub, end_.clone()), start.clone()),
        CmpOp::Lt => {
            let one = Expr::app(
                Expr::const_(Name::from_string("Int.ofNat"), vec![]),
                Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    Expr::const_(Name::from_string("Nat.zero"), vec![]),
                ),
            );
            let start_plus_one = Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Int.add"), vec![]),
                    start.clone(),
                ),
                one,
            );
            Expr::app(Expr::app(int_sub, end_.clone()), start_plus_one)
        }
    };
    mk_nonneg_caseson_false(&nonneg_index, chain_proof)
}

/// Derive `False` from `chain_proof : NonNeg idx` where `idx` reduces to
/// `negSucc k` via the kernel's delta+iota reduction of Int arithmetic.
fn mk_nonneg_caseson_false(nonneg_index: &Expr, chain_proof: &Expr) -> Expr {
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    // Inner motive for Int.casesOn.{1}: fun (_ : Int) => Prop
    let int_cases_motive = Expr::lam(BinderInfo::Default, int_ty.clone(), prop);

    // Branches: ofNat → True, negSucc → False
    let ofnat_branch = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::const_(Name::from_string("True"), vec![]),
    );
    let negsucc_branch = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    // @Int.casesOn.{1} (fun _ => Prop) BVar(1) (fun _ => True) (fun _ => False)
    //
    // Int.casesOn has the Lean-faithful MajorAfterMotive layout:
    //   {motive} -> (major : Int) -> (minor_ofNat) -> (minor_negSucc) -> motive major
    // BVar(1) = x (under 2 binders: outer lambda x, inner lambda _)
    let int_caseson = Expr::const_(
        Name::from_string("Int.casesOn"),
        vec![Level::succ(Level::zero())],
    );
    let motive_body = Expr::app(
        Expr::app(
            Expr::app(Expr::app(int_caseson, int_cases_motive), Expr::bvar(1)),
            ofnat_branch,
        ),
        negsucc_branch,
    );

    // Outer motive: fun (x : Int) (_ : NonNeg x) => <motive_body>
    let nonneg_of_x = Expr::app(
        Expr::const_(Name::from_string("Int.NonNeg"), vec![]),
        Expr::bvar(0), // x, under 1 binder
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        int_ty,
        Expr::lam(BinderInfo::Default, nonneg_of_x, motive_body),
    );

    // mk branch: fun (n : Nat) => True.intro
    let mk_branch = Expr::lam(
        BinderInfo::Default,
        nat_ty,
        Expr::const_(Name::from_string("True.intro"), vec![]),
    );

    // @Int.NonNeg.casesOn motive nonneg_index chain_proof mk_branch
    //
    // casesOn has the Lean-faithful MajorAfterMotive layout:
    //   {motive} -> {i : Int} -> (t : Int.NonNeg i) -> (minor_mk) -> motive i t
    // So the positional order is: motive, index, major, minor.
    //
    // `Int.NonNeg : Int → Prop` is a Prop-valued inductive registered with ZERO
    // level params (order_int.rs: `init_int_ord`), so the kernel's Prop-only
    // elimination gives its `casesOn` NO motive universe param — i.e. ZERO level
    // arguments. Emitting `.{0}` here makes the kernel reject the whole Farkas
    // refutation with `LevelCountMismatch { Int.NonNeg.casesOn, expected: 0, got: 1 }`.
    let nonneg_caseson = Expr::const_(Name::from_string("Int.NonNeg.casesOn"), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(nonneg_caseson, motive), nonneg_index.clone()),
            chain_proof.clone(),
        ),
        mk_branch,
    )
}

/// Build kernel-verified `False` proof for Real sort with concrete non-negative
/// endpoints using `Nat.ble` evaluation and bridge axioms.
///
/// For `Le` (chain proves `Real.ofNat m ≤ Real.ofNat n` where `m > n`):
///   `Real.not_ofNat_le_of_ble_false m n (Eq.refl (Nat.ble m n)) chain_proof`
///   The kernel reduces `Nat.ble m n` to `Bool.false` for concrete `m > n`.
///
/// For `Lt` (chain proves `Real.ofNat m < Real.ofNat n` where `m ≥ n`):
///   `Real.not_ofNat_lt_of_ble_true m n (Eq.refl (Nat.ble n m)) chain_proof`
///   The kernel reduces `Nat.ble n m` to `Bool.true` for concrete `n ≤ m`.
pub(crate) fn mk_real_concrete_false(
    op: CmpOp,
    start_nat: u64,
    end_nat: u64,
    chain_proof: &Expr,
) -> Expr {
    let m_expr = Expr::nat_lit(start_nat);
    let n_expr = Expr::nat_lit(end_nat);
    let nat_ble = Expr::const_(Name::from_string("Nat.ble"), vec![]);
    let bool_ty = Expr::const_(Name::from_string("Bool"), vec![]);
    let eq_refl = Expr::const_(
        Name::from_string("Eq.refl"),
        vec![Level::succ(Level::zero())],
    );

    match op {
        CmpOp::Le => {
            // Nat.ble m n (m > n so this reduces to Bool.false)
            let ble_mn = Expr::app(Expr::app(nat_ble, m_expr.clone()), n_expr.clone());
            let ble_proof = Expr::app(Expr::app(eq_refl, bool_ty), ble_mn);
            let axiom = Expr::const_(Name::from_string("Real.not_ofNat_le_of_ble_false"), vec![]);
            // Real.not_ofNat_le_of_ble_false m n ble_proof chain_proof : False
            Expr::app(
                Expr::app(Expr::app(Expr::app(axiom, m_expr), n_expr), ble_proof),
                chain_proof.clone(),
            )
        }
        CmpOp::Lt => {
            // Nat.ble n m (n ≤ m so this reduces to Bool.true)
            let ble_nm = Expr::app(Expr::app(nat_ble, n_expr.clone()), m_expr.clone());
            let ble_proof = Expr::app(Expr::app(eq_refl, bool_ty), ble_nm);
            let axiom = Expr::const_(Name::from_string("Real.not_ofNat_lt_of_ble_true"), vec![]);
            // Real.not_ofNat_lt_of_ble_true m n ble_proof chain_proof : False
            Expr::app(
                Expr::app(Expr::app(Expr::app(axiom, m_expr), n_expr), ble_proof),
                chain_proof.clone(),
            )
        }
    }
}

/// Build kernel-verified `False` proof for Real sort with concrete integer
/// endpoints (including negative) using `Real.ofInt` bridge axioms.
///
/// The bridge axiom `Real.not_ofInt_le` (or `Real.not_ofInt_lt`) connects a
/// Real-level ordering to an Int-level ordering. The Int-level contradiction
/// is proved using the existing `mk_int_concrete_false` machinery:
///
/// ```text
/// Real.not_ofInt_le a b
///   (λ h : Int.le a b => <NonNeg.casesOn proof>)
///   chain_proof
/// : False
/// ```
///
/// # REQUIRES
///
/// - `a_int` and `b_int` must have type `Int` (the unwrapped integer values
///   inside `Real.ofInt`). Specifically, each must be either `Int.ofNat n` or
///   `Int.negSucc n` for some concrete `Nat` literal `n`.
/// - `chain_proof` must have type `Real.ofInt a_int ≤/< Real.ofInt b_int`
///   (matching `op`) where the bound is violated (i.e., a > b for Le, a >= b
///   for Lt in the mathematical integers).
/// - The bridge axioms `Real.not_ofInt_le` and `Real.not_ofInt_lt` must be
///   registered in the kernel environment.
///
/// # ENSURES
///
/// Returns an `Expr` of type `False`, constructed without `trustedArith`, by
/// reducing the Real-level contradiction to an Int-level contradiction via
/// `NonNeg.casesOn`. The proof term contains a lambda binding the Int-level
/// hypothesis, so the kernel's beta-reduction produces the correct type.
pub(crate) fn mk_real_ofint_concrete_false(
    op: CmpOp,
    a_int: &Expr,
    b_int: &Expr,
    chain_proof: &Expr,
) -> Expr {
    let (axiom_name, int_cmp_name) = match op {
        CmpOp::Le => ("Real.not_ofInt_le", "Int.le"),
        CmpOp::Lt => ("Real.not_ofInt_lt", "Int.lt"),
    };

    // Build the Int-level contradiction proof: λ (h : int_cmp a b) => False
    // using NonNeg.casesOn on h.
    let int_cmp_type = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string(int_cmp_name), vec![]),
            a_int.clone(),
        ),
        b_int.clone(),
    );
    // For Le: mk_int_concrete_false(Le, a_int, b_int, BVar(0))
    //   where BVar(0) = h (the lambda-bound hypothesis of type Int.le a b)
    // For Lt: mk_int_concrete_false(Lt, a_int, b_int, BVar(0))
    let h = Expr::bvar(0);
    let false_body = mk_int_concrete_false(op, a_int, b_int, &h);
    let int_not_proof = Expr::lam(BinderInfo::Default, int_cmp_type, false_body);

    // Real.not_ofInt_le a b int_not_proof chain_proof : False
    let axiom = Expr::const_(Name::from_string(axiom_name), vec![]);
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(axiom, a_int.clone()), b_int.clone()),
            int_not_proof,
        ),
        chain_proof.clone(),
    )
}

// =========================================================================
// Kernel-Expr concrete integer extraction (fallback for ay Var terms)
// =========================================================================

/// Extract a concrete integer value from a kernel Expr pattern.
///
/// Recognizes:
/// - `Int.ofNat(n)` → `n` (non-negative)
/// - `Int.negSucc(n)` → `-(n+1)` (negative)
///
/// The Nat argument `n` may be either a kernel `Literal::Nat` or a
/// constructor-form expression (`Nat.zero`, `Nat.succ`).
///
/// Returns `None` for symbolic or unrecognized expressions.
pub(crate) fn extract_concrete_int_from_expr(expr: &Expr) -> Option<num_bigint::BigInt> {
    use super::theory_lemma_lra_sum_nf::eval_nat_to_bigint;
    use num_bigint::BigInt;
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

/// Check whether a chain's concrete endpoints violate the bound using kernel Expr
/// patterns directly, bypassing ay term-level concrete extraction.
///
/// This is a fallback for cases where ay represents integer constants as named
/// variables (e.g., `mk_var("const5", Sort::Int)`) mapped to concrete kernel
/// expressions via `VariableMapping`. The ay-term-level `extract_concrete_int`
/// only recognizes `Constant::Int`, not `Var` terms, so it returns `None` for
/// these variables even though the underlying kernel Expr IS concrete.
pub(crate) fn is_concrete_violation_by_expr(start_expr: &Expr, end_expr: &Expr, op: CmpOp) -> bool {
    let start = match extract_concrete_int_from_expr(start_expr) {
        Some(v) => v,
        None => return false,
    };
    let end_ = match extract_concrete_int_from_expr(end_expr) {
        Some(v) => v,
        None => return false,
    };
    match op {
        CmpOp::Le => start > end_,
        CmpOp::Lt => start >= end_,
    }
}
