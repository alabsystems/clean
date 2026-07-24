// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::level::Level;

fn make_decidable_eq_goal(ty: Expr, lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Decidable"), vec![]),
        make_eq(ty, lhs, rhs),
    )
}

fn int_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        Expr::nat_lit(n),
    )
}

fn int_neg_succ(n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        Expr::nat_lit(n),
    )
}

fn uint_mk(type_name: &str, n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(&format!("{type_name}.mk")), vec![]),
        Expr::nat_lit(n),
    )
}

/// The genuine v4.30 UInt literal form (`<T>.ofNat n`, δ-unfolds to
/// `<T>.ofBitVec (BitVec.ofNat <w> n)`). The pre-v4.30 `<T>.mk` ctor no longer
/// exists after the BitVec-parity carrier reshape
/// (`designs/2026-07-03-carrier-types-bitvec-parity.md`).
fn uint_ofnat(type_name: &str, n: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string(&format!("{type_name}.ofNat")), vec![]),
        Expr::nat_lit(n),
    )
}

fn fin_mk(bound: u64, val: u64) -> Expr {
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Fin.mk"), vec![]),
                Expr::nat_lit(bound),
            ),
            Expr::nat_lit(val),
        ),
        Expr::const_(Name::from_string("False"), vec![]),
    )
}

fn fin_type(bound: u64) -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Fin"), vec![]),
        Expr::nat_lit(bound),
    )
}

#[test]
fn test_decide_eq_int_mixed_constructor_inequality_no_trusted_axioms() {
    let env = Environment::with_prelude();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let goal = make_decidable_eq_goal(int_ty, int_of_nat(2), int_neg_succ(0));
    let mut state = ProofState::new(env, goal);

    decide_eq(&mut state).expect("Int.ofNat 2 ≠ Int.negSucc 0 should close via Int.noConfusion");
    assert!(
        state.is_complete(),
        "mixed-constructor Int inequality should close"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "Int disequality should not use trusted fallback"
    );

    let proof = state
        .proof_term()
        .expect("closed goal should retain proof term");
    let consts = collect_consts(&proof);
    assert!(consts.contains(&Name::from_string("Int.noConfusion")));
    assert!(
        !consts.contains(&Name::from_string("Nat.noConfusion")),
        "mixed Int constructors should discriminate directly"
    );
}

#[test]
fn test_decide_eq_int_same_constructor_inequality_recurses_to_nat() {
    let env = Environment::with_prelude();
    let int_ty = Expr::const_(Name::from_string("Int"), vec![]);
    let goal = make_decidable_eq_goal(int_ty, int_neg_succ(1), int_neg_succ(2));
    let mut state = ProofState::new(env, goal);

    decide_eq(&mut state).expect("Int.negSucc 1 ≠ Int.negSucc 2 should recurse to Nat.noConfusion");
    assert!(
        state.is_complete(),
        "same-constructor Int inequality should close"
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "Int recursion should stay on kernel path"
    );

    let proof = state
        .proof_term()
        .expect("closed goal should retain proof term");
    let consts = collect_consts(&proof);
    assert!(consts.contains(&Name::from_string("Int.noConfusion")));
    assert!(consts.contains(&Name::from_string("Nat.noConfusion")));
}

#[test]
fn test_build_noconfusion_ne_proof_uint_wrapper_deferred_to_bitvec_migration() {
    // v4.30 BitVec-parity carrier reshape
    // (`designs/2026-07-03-carrier-types-bitvec-parity.md` §2.3a; P0.5 rfl-pin
    // inventory): `UInt*` is now `<T>.ofBitVec (toBitVec : BitVec <w>)` — the old
    // `<T>.mk : Fin <T>.size → <T>` ctor is REMOVED
    // (`data_types_uint.rs` asserts `UInt8.mk` is unregistered). The decide_eq
    // wrapper recogniser `to_uint_view` still keys on `<T>.mk`, and the UInt
    // noConfusion arm feeds a `Nat`-typed continuation — but genuine
    // `<T>.noConfusion` on the reshaped carrier reduces `ofBitVec a = ofBitVec b`
    // to a `BitVec` equality, so the arm needs a BitVec→Fin→Nat rebuild before it
    // can produce a well-typed proof. That consumer migration is DEFERRED (a
    // follow-up brick); real `UInt` disequality is decided axiom-free by the
    // kernel native `<T>.decEq` reducer (`reduce_uint_dec_eq` peeling the BitVec
    // chain — pinned green by the carrier differential harness and
    // `native_reducers_uint` tests), not by this elaborator wrapper.
    //
    // PIN: fed genuine v4.30-shaped operands, the wrapper builder DECLINES
    // (returns `None`) rather than emitting an ill-typed `<T>.mk` proof. When the
    // `to_uint_view` BitVec migration lands, this assertion flips to `Some` — the
    // tripwire that the deferred consumer work has been done. (Same
    // pin-the-current-carrier-state shape as
    // `test_decide_eq_uint8_inequality_no_trusted_axioms` did for the 8f77c6b5
    // Nat→Fin migration.)
    let env = Environment::with_prelude();
    let eq_level = Level::succ(Level::zero());

    for type_name in ["UInt8", "UInt16", "UInt32", "UInt64"] {
        let ty = Expr::const_(Name::from_string(type_name), vec![]);
        let lhs = uint_ofnat(type_name, 3);
        let rhs = uint_ofnat(type_name, 4);
        let proof =
            decide_eq_noconfusion::build_noconfusion_ne_proof(&env, &ty, &lhs, &rhs, &eq_level);
        assert!(
            proof.is_none(),
            "{type_name} noConfusion wrapper builder is not yet migrated to the \
             v4.30 ofBitVec carrier and must DECLINE genuine-shaped operands (got \
             a proof — the deferred to_uint_view BitVec migration may have landed; \
             restore the full typecheck assertion)"
        );
    }
}

#[test]
fn test_decide_eq_uint8_inequality_no_trusted_axioms() {
    // UInt carrier migration (commit 8f77c6b5): the prelude UInt8 is now the
    // faithful Lean 4.8.0 `structure UInt8 where val : Fin UInt8.size`, so the
    // pre-migration bare-Nat form `UInt8.mk (nat_lit 7)` used here is ill-typed
    // (`expected: Fin UInt8.size, inferred: Nat`) and the kernel-strict
    // `close_goal` (#38) correctly REFUSES to close the goal. This pins the
    // soundness gate (no unsound close, no trusted-axiom smuggle) — the same
    // pin shape as `test_decide_eq_fin_mismatch_no_trusted_axioms` below.
    // Restoring an axiom-free CLOSE for UInt8 disequalities needs (a) the
    // decide_eq wrapper recursion to type the `.mk` field as `Fin <T>.size`
    // instead of `Nat` (decide_eq_noconfusion.rs UInt arm), and (b) a real
    // `Nat.lt` isLt witness for `Fin.mk` literals — the same follow-up already
    // tracked for the Fin lane.
    let env = Environment::with_prelude();
    let uint8_ty = Expr::const_(Name::from_string("UInt8"), vec![]);
    let goal = make_decidable_eq_goal(uint8_ty, uint_mk("UInt8", 7), uint_mk("UInt8", 9));
    let mut state = ProofState::new(env, goal);

    let result = decide_eq(&mut state);
    assert!(
        result.is_err(),
        "decide_eq must reject the pre-Fin-carrier bare-Nat UInt8.mk proof \
         (kernel-strict close_goal; UInt carrier migration 8f77c6b5), got Ok \
         with state complete={}",
        state.is_complete()
    );
    assert_eq!(
        state.trusted_axiom_count(),
        0,
        "refused UInt8 disequality must not fall back to a trusted axiom"
    );
}

#[test]
fn test_build_noconfusion_ne_proof_typechecks_for_fin_wrapper_recursion() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let eq_level = Level::succ(Level::zero());
    let ty = fin_type(3);
    let lhs = fin_mk(3, 0);
    let rhs = fin_mk(3, 1);
    let proof = decide_eq_noconfusion::build_noconfusion_ne_proof(&env, &ty, &lhs, &rhs, &eq_level)
        .expect("Fin.mk 0 ≠ Fin.mk 1 should produce a proof");
    let inferred = tc
        .infer_type(&proof)
        .expect("Fin wrapper proof should typecheck");
    let expected = Expr::pi(
        BinderInfo::Default,
        decide_eq_noconfusion::mk_eq_expr(&ty, &lhs, &rhs, &eq_level),
        Expr::const_(Name::from_string("False"), vec![]),
    );

    assert!(
        tc.is_def_eq(&inferred, &expected),
        "Fin wrapper proof type mismatch:\n  inferred: {inferred:?}\n  expected: {expected:?}"
    );

    let consts = collect_consts(&proof);
    assert!(consts.contains(&Name::from_string("Fin.noConfusion")));
    assert!(consts.contains(&Name::from_string("Nat.noConfusion")));
}

#[test]
fn test_decide_eq_fin_mismatch_no_trusted_axioms() {
    // #38 / #9: decide_eq's `Fin.mk 0 _ ≠ Fin.mk 1 _` term is ill-typed — the
    // `Fin.mk` constructors carry an `isLt : Nat.lt val 2` proof field, and the
    // tactic supplies a `Sort`/placeholder where that `Nat.lt 0 2` proof is
    // required (inferred `Sort(Zero)` vs expected `Nat.lt 0 2`). The kernel's
    // strict (`infer_only=false`) check that `close_goal` now performs rejects
    // this App argument exactly as `Environment::add_decl` would, so `decide_eq`
    // correctly REFUSES to emit the unsound proof. Previously the lenient
    // `infer_only=true` close accepted the kernel-invalid term. Emitting a real
    // `Nat.lt` isLt witness is tracked separately; this test pins the soundness
    // gate (no unsound close).
    let env = Environment::with_prelude();
    let fin_ty = fin_type(2);
    let goal = make_decidable_eq_goal(fin_ty, fin_mk(2, 0), fin_mk(2, 1));
    let mut state = ProofState::new(env, goal);

    let result = decide_eq(&mut state);
    assert!(
        result.is_err(),
        "decide_eq must reject the ill-typed Fin noConfusion proof \
         (kernel-strict close_goal), got Ok with state complete={}",
        state.is_complete()
    );
}
