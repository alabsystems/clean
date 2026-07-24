// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! E3 cross-width BitVec conflation: adversarial soundness regression.
//!
//! Background (diagnosis E3, task #46). The native reducer
//! `reduce_bitvec_of_nat` collapses `BitVec.ofNat n i` to a BARE `Nat` literal
//! `i % 2^n` (see `native_reducers_bitvec.rs`). The width `n` survives only in
//! the TYPE (`App(BitVec, n)`), never in the reduced VALUE. Consequently two
//! same-payload BitVecs of DIFFERENT widths whnf to the identical `Lit(Nat v)`,
//! so the RAW value-level `is_def_eq(BitVec.ofNat 8 5, BitVec.ofNat 16 5)`
//! returns `true`. That is a genuine raw-`is_def_eq` artifact.
//!
//! It is NOT an exploitable soundness hole on the verified `add_decl` /
//! `check_type` re-verification path (the path `verify-batch` / `clean check`
//! use). `add_decl` FIRST runs `infer_sort(type_)` on the STATED type with
//! `infer_only = false`; in that mode the App-argument check fires on the `Eq`
//! application. The third `Eq` argument `BitVec.ofNat 16 5` infers to
//! `BitVec 16`, the expected (instantiated) argument type is `BitVec 8`, and
//! `is_def_eq(BitVec 16, BitVec 8)` compares the TYPES `App(BitVec,16)` vs
//! `App(BitVec,8)` — where `16 ≠ 8` as `Nat` literals — NOT the conflatable
//! bare-`Nat` payloads. So the ill-typed cross-width stated type is REJECTED
//! before the payload def-eq is ever reached.
//!
//! These tests PIN that closure so a future change that weakens
//! `infer_sort` / the App-argument check — or that routes re-verification
//! through a `check_type` path lacking the stated-type sort gate — cannot
//! silently re-open the hole:
//!
//!   1. RAW ARTIFACT (documented, expected `true`): the value-level
//!      `is_def_eq(ofNat 8 5, ofNat 16 5) = true`, while the same-width
//!      controls behave correctly (`ofNat 8 5 == ofNat 8 5` true,
//!      `ofNat 8 5 == ofNat 8 6` false).
//!   2. TYPE-LEVEL GUARD: `is_def_eq(BitVec 8, BitVec 16) = false`.
//!   3. THE SAFETY PROPERTY: `add_decl` of the doctored cross-width false
//!      theorem `@Eq (BitVec 8) (ofNat 8 5) (ofNat 16 5) := rfl` is REJECTED,
//!      while the same-width control `@Eq (BitVec 8) (ofNat 8 5) (ofNat 8 5)
//!      := rfl` is ACCEPTED (the gate is specific, not over-rejecting).
//!   4. `check_type` / `infer_sort` mirror (3) directly.
//!
//! NOTE: This is a documentation/regression pin, NOT a kernel change. Per the
//! E3 diagnosis the bare-`Nat` value representation of BitVec/UInt is a
//! deliberate kernel choice that the UInt/BitVec coercion lanes depend on;
//! cross-width soundness is enforced at the TYPE level by the stated-type
//! `infer_sort` gate, which these tests lock down.

use crate::env::{Declaration, Environment};
use crate::expr::Expr;
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Build the standard prelude environment. It now seeds both the genuine
/// `BitVec : (w : Nat) → Type` carrier and the kernel-checked
/// `BitVec.ofNat : (w n : Nat) → BitVec w` definition. The native reducer still
/// drives value-level reduction by constant name, so the E3 raw-conflation
/// premise remains unchanged: the width is erased to a bare `Nat` literal in
/// the reduced VALUE while the genuine `BitVec w` TYPE keeps its width.
fn make_bitvec_env() -> Environment {
    Environment::with_prelude()
}

/// `BitVec w` as a type expression.
fn bitvec(w: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("BitVec"), vec![]),
        Expr::nat_lit(w),
    )
}

/// `BitVec.ofNat w v`.
fn of_nat(w: u64, v: u64) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("BitVec.ofNat"), vec![]),
        [Expr::nat_lit(w), Expr::nat_lit(v)],
    )
}

/// `@Eq (BitVec w) lhs rhs` (sort of `BitVec w` is `Sort 1`, so the `Eq`
/// universe parameter is `1`).
fn eq_bitvec(w: u64, lhs: Expr, rhs: Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [bitvec(w), lhs, rhs],
    )
}

/// `@Eq.refl (BitVec w) v`.
fn eq_refl_bitvec(w: u64, v: Expr) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [bitvec(w), v],
    )
}

// ===========================================================================
// (1) RAW is_def_eq ARTIFACT — documented, expected `true`.
// ===========================================================================

/// The known raw artifact: the value-level reducer drops the width, so
/// `is_def_eq(BitVec.ofNat 8 5, BitVec.ofNat 16 5)` is `true`. This is the
/// payload-conflation the type-level gate (test 3/4) renders unreachable as a
/// false-proposition certification. Pinned so a regression here is noticed.
#[test]
fn test_raw_is_def_eq_crosswidth_payload_conflates_true_known_artifact() {
    let env = make_bitvec_env();
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&of_nat(8, 5), &of_nat(16, 5)),
        "KNOWN ARTIFACT: BitVec.ofNat erases width to a bare Nat, so cross-width \
         same-payload VALUES conflate at raw is_def_eq. If this changed (now \
         false), the width-tagging hardening (fix_plan option 1) may have landed \
         — update this pin and the SOUNDNESS_CERTIFICATE note accordingly."
    );
}

/// Same-width controls: the value reducer is otherwise faithful —
/// `ofNat 8 5 == ofNat 8 5` (true) and `ofNat 8 5 != ofNat 8 6` (false).
#[test]
fn test_raw_is_def_eq_same_width_is_faithful() {
    let env = make_bitvec_env();
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(&of_nat(8, 5), &of_nat(8, 5)),
        "same width + same payload must be def-eq"
    );
    assert!(
        !tc.is_def_eq(&of_nat(8, 5), &of_nat(8, 6)),
        "same width + different payload must NOT be def-eq"
    );
}

// ===========================================================================
// (2) TYPE-LEVEL GUARD — the widths are distinct at the type level.
// ===========================================================================

/// The TYPES `BitVec 8` and `BitVec 16` are NOT def-eq: `8 ≠ 16` as `Nat`
/// literals (no width erasure happens on the type argument). This is the
/// guard the App-argument check in `infer_sort` leans on.
#[test]
fn test_bitvec_type_crosswidth_is_not_def_eq() {
    let env = make_bitvec_env();
    let tc = TypeChecker::new(&env);
    assert!(
        !tc.is_def_eq(&bitvec(8), &bitvec(16)),
        "BitVec 8 and BitVec 16 are DISTINCT types; the width is preserved on the \
         type argument even though it is erased on the value"
    );
    assert!(
        tc.is_def_eq(&bitvec(8), &bitvec(8)),
        "BitVec 8 is def-eq to itself"
    );
}

// ===========================================================================
// (3) THE SAFETY PROPERTY — add_decl REJECTS the cross-width false theorem,
//     ACCEPTS the same-width control.
// ===========================================================================

/// Exploit attempt: the doctored false theorem
/// `e3_bad : @Eq (BitVec 8) (BitVec.ofNat 8 5) (BitVec.ofNat 16 5)
///         := @Eq.refl (BitVec 8) (BitVec.ofNat 8 5)`.
///
/// Even though the proof's payloads conflate under the value reducer, the
/// STATED type is ill-typed: its third `Eq` argument `BitVec.ofNat 16 5` has
/// type `BitVec 16 ≠ BitVec 8`. `add_decl` runs `infer_sort` on the stated
/// type first (`infer_only = false`), whose App-argument check rejects the
/// cross-width mismatch BEFORE any payload def-eq is reached. This MUST error.
#[test]
fn test_crosswidth_false_theorem_add_decl_rejects() {
    let mut env = make_bitvec_env();
    let stated = eq_bitvec(8, of_nat(8, 5), of_nat(16, 5));
    let proof = eq_refl_bitvec(8, of_nat(8, 5));
    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("e3_bad"),
        level_params: vec![],
        type_: stated,
        value: proof,
    });
    assert!(
        result.is_err(),
        "add_decl accepted a cross-width BitVec false theorem — the stated-type \
         infer_sort gate that closes E3 has regressed: {result:?}"
    );
}

/// Positive control: the same-width theorem
/// `@Eq (BitVec 8) (BitVec.ofNat 8 5) (BitVec.ofNat 8 5) := rfl` is
/// well-typed and MUST be accepted — the gate is SPECIFIC to the cross-width
/// case and is not over-rejecting valid same-width BitVec equalities.
#[test]
fn test_same_width_theorem_add_decl_accepts() {
    let mut env = make_bitvec_env();
    let stated = eq_bitvec(8, of_nat(8, 5), of_nat(8, 5));
    let proof = eq_refl_bitvec(8, of_nat(8, 5));
    let result = env.add_decl(Declaration::Theorem {
        name: Name::from_string("e3_ok"),
        level_params: vec![],
        type_: stated,
        value: proof,
    });
    assert!(
        result.is_ok(),
        "add_decl wrongly REJECTED a valid same-width BitVec equality — the \
         E3 gate is over-rejecting: {result:?}"
    );
}

// ===========================================================================
// (4) check_type / infer_sort mirror — direct re-verify entry points.
// ===========================================================================

/// `infer_sort` on the cross-width stated type rejects directly (this is the
/// exact call `add_decl` makes first). The same-width stated type sorts fine.
#[test]
fn test_crosswidth_stated_type_infer_sort_rejects() {
    let env = make_bitvec_env();
    let tc = TypeChecker::new(&env);
    let bad = eq_bitvec(8, of_nat(8, 5), of_nat(16, 5));
    assert!(
        tc.infer_sort(&bad).is_err(),
        "infer_sort accepted an ill-typed cross-width Eq stated type"
    );
    let good = eq_bitvec(8, of_nat(8, 5), of_nat(8, 5));
    assert!(
        tc.infer_sort(&good).is_ok(),
        "infer_sort wrongly rejected a well-typed same-width Eq stated type"
    );
}

/// `check_type(proof, stated)` ALONE infers the proof type and only checks it
/// against `stated` up to def-eq; because the conflatable payloads whnf to the
/// same bare `Nat`, this lenient path can ACCEPT the doctored proof. That is
/// precisely WHY the real acceptance path (`add_decl`) must — and does — run
/// the stated-type `infer_sort` gate first. We assert the documented behaviour
/// so the leniency boundary is explicit and any future tightening of
/// `check_type` is observed.
#[test]
fn test_check_type_alone_is_lenient_documents_why_add_decl_gates_first() {
    let env = make_bitvec_env();
    let tc = TypeChecker::new(&env);
    let stated = eq_bitvec(8, of_nat(8, 5), of_nat(16, 5));
    let proof = eq_refl_bitvec(8, of_nat(8, 5));
    // Documented: check_type does NOT re-sort the stated type, so the payload
    // conflation lets it through. add_decl (test 3) is the gate that closes E3.
    let lenient = tc.check_type(&proof, &stated).is_ok();
    let gated = {
        let mut env2 = make_bitvec_env();
        env2.add_decl(Declaration::Theorem {
            name: Name::from_string("e3_bad_gatecheck"),
            level_params: vec![],
            type_: stated.clone(),
            value: proof.clone(),
        })
        .is_err()
    };
    assert!(
        gated,
        "add_decl MUST reject the cross-width false theorem regardless of \
         check_type leniency"
    );
    // If check_type alone ever STOPS being lenient (starts rejecting here),
    // that is a strict improvement — record it rather than failing.
    if !lenient {
        eprintln!(
            "note: check_type alone now rejects the cross-width payload \
             conflation (stricter than the documented E3 baseline)"
        );
    }
}
