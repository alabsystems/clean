// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The closed `Int`-predecessor fold, and the guard behind it.**
//!
//! `import Init.GrindInstances` re-checks the `Int32`/`Int64`/`BitVec`
//! conversion lemmas. Measured 2026-08-26 at `69f4f4a70`, that import reached
//! **10.4 GB RSS in 13 s** and was killed: **599,888 of 600,000** ι-expansions
//! over a large literal were one recursor —
//!
//! ```text
//! Nat.rec (fun _ => Int) z (fun _ ih => ih - 1) (2^32)
//! ```
//!
//! — its count decrementing by exactly 1 per expansion, i.e. ~4.3 billion unary
//! steps. Two things close it, and this file pins both:
//!
//! 1. [`TypeChecker::reduce_int_pred_fold`] COMPUTES that fold as `z - N`, so
//!    the common case still yields a literal.
//! 2. [`TypeChecker::native_closed_fold_grind_stuck`] leaves the *rest* of the
//!    family stuck rather than walking it.
//!
//! The discriminator for (2) is **whether the step consumes its induction
//! hypothesis**, never the count's magnitude — see
//! `tests2/iota_one_step_wide_major.rs`, which holds the `clean-verify` EvalIR
//! shapes that a magnitude-keyed guard would break.

use crate::env::Environment;
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn int_ty() -> Expr {
    c("Int")
}

fn nat_ty() -> Expr {
    c("Nat")
}

/// `Nat.rec` / `Int.rec` at `Sort 1` — every motive here returns `Int : Type`.
fn rec_at_type(name: &str) -> Expr {
    Expr::const_(n(name), vec![Level::succ(Level::zero())])
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn env_with_int() -> Environment {
    let mut env = Environment::new();
    env.init_int().expect("Int seeds");
    env
}

/// `fun (a : Nat) => Nat.rec (fun _ : Nat => Int) (Int.negSucc Nat.zero)
///                           (fun (m : Nat) (_ : Int) => Int.ofNat m) a`
///
/// The `Int.ofNat` branch of the predecessor: `0 ↦ -1`, `m+1 ↦ Int.ofNat m`.
fn of_nat_pred_case() -> Expr {
    lam(
        nat_ty(),
        Expr::apps(
            rec_at_type("Nat.rec"),
            [
                lam(nat_ty(), int_ty()),
                Expr::app(c("Int.negSucc"), c("Nat.zero")),
                lam(
                    nat_ty(),
                    lam(int_ty(), Expr::app(c("Int.ofNat"), Expr::bvar(1))),
                ),
                Expr::bvar(0),
            ],
        ),
    )
}

/// `fun (b : Nat) => Int.negSucc (Nat.succ b)` — the `Int.negSucc` branch.
fn neg_succ_pred_case() -> Expr {
    lam(
        nat_ty(),
        Expr::app(c("Int.negSucc"), Expr::app(c("Nat.succ"), Expr::bvar(0))),
    )
}

/// `fun (_ : Nat) (ih : Int) => ih - 1`, spelled as the `Int.rec` case split the
/// elaborator emits. This is the shape measured in `Init.GrindInstances`.
fn int_pred_step() -> Expr {
    lam(
        nat_ty(),
        lam(
            int_ty(),
            Expr::apps(
                rec_at_type("Int.rec"),
                [
                    lam(int_ty(), int_ty()),
                    of_nat_pred_case(),
                    neg_succ_pred_case(),
                    Expr::bvar(0),
                ],
            ),
        ),
    )
}

/// `Nat.rec (fun _ => Int) z step count`.
fn int_fold(z: Expr, step: Expr, count: Expr) -> Expr {
    Expr::apps(
        rec_at_type("Nat.rec"),
        [lam(nat_ty(), int_ty()), z, step, count],
    )
}

fn int_of_nat(v: u64) -> Expr {
    Expr::app(c("Int.ofNat"), Expr::nat_lit(v))
}

/// Read a whnf'd closed `Int` as an `i128`, or `None` if it is not a literal
/// constructor application (i.e. the term is stuck).
fn as_int(e: &Expr) -> Option<i128> {
    let ExprKind::App(f, arg) = &e.kind else {
        return None;
    };
    let ExprKind::Const(name, _) = &f.kind else {
        return None;
    };
    let ExprKind::Lit(Literal::Nat(BigNat::Small(v))) = &arg.kind else {
        return None;
    };
    if *name == n("Int.ofNat") {
        Some(i128::from(*v))
    } else if *name == n("Int.negSucc") {
        Some(-(i128::from(*v) + 1))
    } else {
        None
    }
}

/// **The reproducer, in milliseconds.** `2^32` iterations of `ih - 1` starting
/// from `2^31` — verbatim the `Int32.minValue.toInt` fold — must produce
/// `-2^31`, not 4.3 billion ι-steps.
#[test]
fn test_int_pred_fold_at_the_import_trigger_count_computes() {
    let env = env_with_int();
    let tc = TypeChecker::new(&env);

    let two_31: u64 = 1 << 31;
    let two_32: u64 = 1 << 32;
    let e = int_fold(int_of_nat(two_31), int_pred_step(), Expr::nat_lit(two_32));

    let reduced = tc.whnf(&e);
    assert_eq!(
        as_int(&reduced),
        Some(-(i128::from(two_31))),
        "2^31 - 2^32 must reduce to -2^31; got {reduced:?}"
    );
}

/// The canonical closed `Int` expression for `v`.
fn int_lit(v: i128) -> Expr {
    if v < 0 {
        Expr::app(
            c("Int.negSucc"),
            Expr::nat_lit(u64::try_from(-v - 1).expect("test magnitudes fit u64")),
        )
    } else {
        Expr::app(
            c("Int.ofNat"),
            Expr::nat_lit(u64::try_from(v).expect("test magnitudes fit u64")),
        )
    }
}

/// **The reducer agrees with plain ι.** Below the threshold the ordinary
/// recursor path runs untouched; this pins that it computes the same value the
/// reducer mints, over both signs and across zero.
///
/// The comparison is `is_def_eq`, not syntactic: plain ι leaves the negative
/// side as an *unnormalized* `Int.negSucc (Nat.succ … (Nat.succ 0))` tower,
/// while the reducer mints the canonical `Int.negSucc <literal>`. The two are
/// definitionally equal — which is exactly what the reducer is allowed to do.
#[test]
fn test_int_pred_fold_agrees_with_plain_iota_below_threshold() {
    let env = env_with_int();
    let tc = TypeChecker::new(&env);

    // All counts < 512, so `reduce_int_pred_fold` declines and plain ι runs.
    for (z, count) in [(30u64, 100u64), (100, 100), (100, 7), (0, 200), (500, 1)] {
        let want = i128::from(z) - i128::from(count);
        let plain = int_fold(int_of_nat(z), int_pred_step(), Expr::nat_lit(count));
        assert!(
            tc.is_def_eq(&plain, &int_lit(want)),
            "plain iota: {z} - {count} should be {want}, got {:?}",
            tc.whnf(&plain)
        );
    }

    // At 4096 the reducer fires; same arithmetic, canonical literal form.
    let folded = tc.whnf(&int_fold(
        int_of_nat(30),
        int_pred_step(),
        Expr::nat_lit(4096),
    ));
    assert_eq!(as_int(&folded), Some(-4066), "30 - 4096 = -4066");
}

/// Crossing zero is where the two `Int` constructors meet, so pin both signs
/// and the boundary exactly.
#[test]
fn test_int_pred_fold_sign_boundary() {
    let env = env_with_int();
    let tc = TypeChecker::new(&env);

    for (z, count, want) in [
        (5000u64, 1000u64, 4000i128), // stays non-negative
        (1000, 1000, 0),              // lands exactly on zero
        (1000, 1001, -1),             // first negative
        (0, 1024, -1024),             // wholly negative
    ] {
        let got = tc.whnf(&int_fold(
            int_of_nat(z),
            int_pred_step(),
            Expr::nat_lit(count),
        ));
        assert_eq!(
            as_int(&got),
            Some(want),
            "{z} - {count} should be {want}; got {got:?}"
        );
    }
}

/// **Negative control for the reducer.** A fold with the SAME motive, count and
/// accumulator but a step that is NOT the predecessor must not be folded as one.
/// Here the step is the IDENTITY on `ih`, so the true value is `z`, not `z - N`.
/// A matcher that keyed on "motive is `Int` and the count is big" would mint
/// `z - N` here and be unsound.
#[test]
fn test_identity_step_is_not_read_as_a_predecessor() {
    let env = env_with_int();
    let tc = TypeChecker::new(&env);

    // fun (_ : Nat) (ih : Int) => ih
    let identity_step = lam(nat_ty(), lam(int_ty(), Expr::bvar(0)));
    let e = int_fold(int_of_nat(77), identity_step, Expr::nat_lit(1 << 17));

    let reduced = tc.whnf(&e);
    assert_ne!(
        as_int(&reduced),
        Some(77 - (1 << 17)),
        "the identity step must never be folded as `z - N`"
    );
    // It consumes its `ih`, so the grind guard leaves it stuck rather than
    // walking 2^20 steps. Stuck is sound (narrowing); a wrong literal is not.
    assert!(
        as_int(&reduced).is_none(),
        "expected the fold to be left stuck, got the value {:?}",
        as_int(&reduced)
    );
}

/// **The guard fires** on a large closed fold whose step consumes its induction
/// hypothesis and is not the pinned predecessor — the `Prod Nat Nat`
/// accumulator class measured alongside the `Int` one (399,878 events).
#[test]
fn test_large_closed_ih_consuming_fold_is_left_stuck() {
    let env = env_with_int();
    let tc = TypeChecker::new(&env);

    // fun (_ : Nat) (ih : Int) => Int.negSucc (Nat.succ ih')  -- uses ih
    let step = lam(
        nat_ty(),
        lam(
            int_ty(),
            Expr::apps(
                rec_at_type("Int.rec"),
                [
                    lam(int_ty(), int_ty()),
                    // fun a => Int.ofNat (Nat.succ a)   (i.e. ih + 1, not -1)
                    lam(
                        nat_ty(),
                        Expr::app(c("Int.ofNat"), Expr::app(c("Nat.succ"), Expr::bvar(0))),
                    ),
                    neg_succ_pred_case(),
                    Expr::bvar(0),
                ],
            ),
        ),
    );
    let e = int_fold(int_of_nat(0), step, Expr::nat_lit(1 << 17));

    let reduced = tc.whnf(&e);
    assert!(
        matches!(&reduced.kind, ExprKind::App(..))
            && matches!(&reduced.get_app_fn().kind, ExprKind::Const(name, _) if *name == n("Nat.rec")),
        "a 2^17-step ih-consuming fold must be left stuck at the Nat.rec application, \
         got {reduced:?}"
    );
}

/// **Negative control for the guard** — the property `iota_one_step_wide_major.rs`
/// exists to protect, restated at the `Int` motive: a step that DISCARDS its
/// induction hypothesis is a `Nat.casesOn` in disguise, reduces in ONE ι-step at
/// any count, and must keep doing so.
#[test]
fn test_ih_discarding_step_still_reduces_at_a_huge_count() {
    let env = env_with_int();
    let tc = TypeChecker::new(&env);

    // fun (m : Nat) (_ : Int) => Int.ofNat m   — `Int.negOfNat`-shaped.
    let discarding = lam(
        nat_ty(),
        lam(int_ty(), Expr::app(c("Int.ofNat"), Expr::bvar(1))),
    );
    let count: u64 = 1 << 32;
    let e = int_fold(int_of_nat(0), discarding, Expr::nat_lit(count));

    let reduced = tc.whnf(&e);
    assert_eq!(
        as_int(&reduced),
        Some(i128::from(count) - 1),
        "the ih-discarding fold decides on the first iota step at ANY count; a guard \
         keyed on the count's magnitude would leave it stuck as {reduced:?}"
    );
}
