// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `Nat.le_of_ble_eq_true` is PARKED (irreducible), and the `Char` projection
//! that used to unwind it still means the same thing.
//!
//! That lemma is `(Nat.rec C base step b) a h` with a `Nat.succ_le_succ` step,
//! so reducing it to a `Nat.le` CONSTRUCTOR unwinds min(a, b) layers. Nothing
//! needs that — it is a PROOF — and the only thing that ever demanded the
//! constructor was another recursor eliminating it. `Char.ofNatAux` derives its
//! width bound through `Nat.le_trans`, which is `Nat.le.rec` on exactly this
//! lemma, so every `Char` below the surrogate block paid min(55296, 2^32) =
//! 55,296 layers: `theorem : (Char.ofNat 65).val = 65 := rfl` cost 4.93 GB and
//! 21 s, and cost the same at 1 and at 300 because the constant is the bound,
//! not the code point. Parked, it is 0.05 GB.
//!
//! These arms pin the MECHANISM and the MEANING, not a timing: the defect was a
//! slow accept, so a timing assertion would be flaky where this is exact.

use crate::env::{Environment, Reducibility};
use crate::expr::Expr;
use crate::name::Name;
use crate::tc::TypeChecker;

fn nm(s: &str) -> Name {
    Name::from_string(s)
}

#[test]
fn test_nat_le_of_ble_eq_true_is_parked() {
    let env = Environment::try_with_prelude().expect("native prelude");
    assert_eq!(
        env.get_reducibility(&nm("Nat.le_of_ble_eq_true")),
        Some(Reducibility::Irreducible),
        "the bridge proof must stay parked; unparking it re-opens a \
         min(a,b)-layer unwind on every Char projection"
    );
}

#[test]
fn test_the_lemma_is_still_a_registered_theorem() {
    // Parking changes the reduction STRATEGY, not the theory. The lemma must
    // still be present and typed, or callers that merely CITE it break.
    let env = Environment::try_with_prelude().expect("native prelude");
    let info = env
        .get_const(&nm("Nat.le_of_ble_eq_true"))
        .expect("Nat.le_of_ble_eq_true must still be registered");
    assert!(
        info.value.is_some(),
        "it is a Theorem and keeps its proof term; parking only stops delta"
    );
}

#[test]
fn test_char_projection_still_means_what_it_meant() {
    // THE MEANING HALF. Parking can only make def-eq more conservative, so the
    // hazard is a false REJECTION. This is the equality the whole defect was
    // about: it must still hold.
    let env = Environment::try_with_prelude().expect("native prelude");
    let tc = TypeChecker::new(&env);

    let char_of_nat_65 = Expr::app(Expr::const_(nm("Char.ofNat"), vec![]), Expr::nat_lit(65));
    let lhs = Expr::app(Expr::const_(nm("Char.val"), vec![]), char_of_nat_65);
    let rhs = Expr::app(Expr::const_(nm("UInt32.ofNat"), vec![]), Expr::nat_lit(65));

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "(Char.ofNat 65).val must still be def-eq to UInt32.ofNat 65"
    );
}

#[test]
fn test_char_projection_still_refuses_a_wrong_value() {
    // The other direction, so the arm above cannot be satisfied by a def-eq
    // that accepts everything.
    let env = Environment::try_with_prelude().expect("native prelude");
    let tc = TypeChecker::new(&env);

    let char_of_nat_65 = Expr::app(Expr::const_(nm("Char.ofNat"), vec![]), Expr::nat_lit(65));
    let lhs = Expr::app(Expr::const_(nm("Char.val"), vec![]), char_of_nat_65);
    let wrong = Expr::app(Expr::const_(nm("UInt32.ofNat"), vec![]), Expr::nat_lit(66));

    assert!(
        !tc.is_def_eq(&lhs, &wrong),
        "(Char.ofNat 65).val must NOT be def-eq to UInt32.ofNat 66"
    );
}

#[test]
fn test_char_to_nat_is_unaffected() {
    // `Char.toNat` reaches the code point through a Nat-typed projection chain
    // that discards the `isLt` proof, so it never entered the derivation and
    // must be unchanged.
    let env = Environment::try_with_prelude().expect("native prelude");
    let tc = TypeChecker::new(&env);

    let char_of_nat_65 = Expr::app(Expr::const_(nm("Char.ofNat"), vec![]), Expr::nat_lit(65));
    let lhs = Expr::app(Expr::const_(nm("Char.toNat"), vec![]), char_of_nat_65);

    assert!(
        tc.is_def_eq(&lhs, &Expr::nat_lit(65)),
        "Char.toNat (Char.ofNat 65) must still reduce to 65"
    );
}
