// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **The ONE-STEP recursor over a WIDE literal major** — the shape every
//! candidate fix for the `import Init` explosion must leave alone.
//!
//! # Why this file exists
//!
//! A bare `import Init` explodes to 16 GB because `Nat.decEq` at `2^32`
//! delta-unfolds into its `Nat.rec` seed and is walked one iota step at a time.
//! The obvious guard — refuse iota when the major premise is a large closed
//! literal — was written (`78d86fb51`), fixed imports completely (62 s / 3 GB),
//! and was REVERTED (`9c65aa045`) because it reddened
//! `clean-verify --test axiom_refutation_gate`, 8 failed / 0 passed.
//!
//! That gate takes ~12 minutes to build and run. **This file is the same
//! refutation in milliseconds.**
//!
//! # The shape
//!
//! `clean-verify`'s EvalIR substrate (`spec/core_spec/eval_ir_bits.rs`,
//! `eval_ir_state.rs`) is built on a deliberate idiom: a `Nat.rec` whose
//! successor minor **discards its induction hypothesis**, so the whole
//! computation is ONE iota step no matter how wide the major is. The kernel's
//! `nat_lit_to_constructor` peels `Lit(n)` to `Nat.succ (Lit (n-1))` lazily —
//! one `BigNat::pred()` — and the minor throws the recursive call away, so
//! nothing further unfolds.
//!
//! ```text
//! ir_nat_dbl n = Nat.rec (fun _ => Nat) 0 (fun p _ => succ (p + succ p)) n
//! ir_nat_pos n = Nat.rec (fun _ => Bool) false (fun _ _ => true)          n
//! ```
//!
//! `ir_nat_pos` is what `ir_nat_ltb a b := ir_nat_pos (Nat.sub b a)` runs, so
//! the idiom is not one witness — it is the comparison engine underneath
//! `ir_nat_bitlen`, `ir_dm_step2`, `ir_dm_go`, `ir_nat_divmod`, `ir_nat_mulb`,
//! `ir_nat_min` and `ir_nat_max`. `ir_nat_eqb`'s own registered note says the
//! point out loud: "the u32 sentinel pair — 4.29e9 walk steps — costs two
//! BigNat subtractions".
//!
//! # The discriminator, stated so a future fix can key on it
//!
//! `Nat.decEq`'s tower and these are **not** distinguishable by the major's
//! magnitude: imports need `2^32` blocked and `ir_nat_dbl_w` needs `2^53`
//! allowed, so no threshold on the major separates them. They ARE
//! distinguishable by whether the successor minor **uses** its induction
//! hypothesis. `Nat.decEq` does (that is the walk); every EvalIR primitive
//! here does not (`test_the_wide_major_minors_discard_their_ih` pins it).
//!
//! # Failure mode
//!
//! A guard that refuses these leaves the application STUCK — it does not merely
//! slow down. So these assertions fail instantly and cheaply; nothing here can
//! hang.

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind, Literal};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// `2^53 - 1`, the binary64 significand bound and the argument
/// `ir_nat_dbl_w` uses.
const TWO_POW_53_MINUS_1: u64 = 9_007_199_254_740_991;

/// `2 * (2^53 - 1)`, the literal `ir_nat_dbl_w` asserts by `Eq.refl`.
const TWO_POW_54_MINUS_2: u64 = 18_014_398_509_481_982;

/// `2^32`, the major of the `Nat.decEq` tower that explodes `import Init`.
const TWO_POW_32: u64 = 4_294_967_296;

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn bool_ty() -> Expr {
    Expr::const_(Name::from_string("Bool"), vec![])
}

fn nat_succ(e: Expr) -> Expr {
    Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), e)
}

fn nat_add(a: Expr, b: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), a),
        b,
    )
}

/// `Nat.rec` at `Sort 1` — every motive here returns `Nat` or `Bool`, both
/// `Type = Sort 1`.
fn nat_rec() -> Expr {
    Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    )
}

/// An environment with `Nat` (and its recursor) and `Bool` seeded.
fn nat_bool_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("Nat seeds");
    env.init_bool().expect("Bool seeds");
    env
}

/// The successor minor of `ir_nat_dbl`:
/// `fun (p : Nat) (_ : Nat) => Nat.succ (Nat.add p (Nat.succ p))`.
///
/// De Bruijn: inside the inner lambda, `p` is `BVar(1)` and the discarded
/// induction hypothesis is `BVar(0)`.
fn ir_nat_dbl_succ_minor() -> Expr {
    let p = Expr::bvar(1);
    Expr::lam(
        BinderInfo::Default,
        nat_ty(),
        Expr::lam(
            BinderInfo::Default,
            nat_ty(),
            nat_succ(nat_add(p.clone(), nat_succ(p))),
        ),
    )
}

/// `ir_nat_dbl n`, verbatim from `clean-verify`'s registered source.
fn ir_nat_dbl(n: Expr) -> Expr {
    Expr::apps(
        nat_rec(),
        [
            // motive: fun (_ : Nat) => Nat
            Expr::lam(BinderInfo::Default, nat_ty(), nat_ty()),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
            ir_nat_dbl_succ_minor(),
            n,
        ],
    )
}

/// The successor minor of `ir_nat_pos`:
/// `fun (_ : Nat) (_ : Bool) => Bool.true`. Discards BOTH the predecessor and
/// the induction hypothesis.
fn ir_nat_pos_succ_minor() -> Expr {
    Expr::lam(
        BinderInfo::Default,
        nat_ty(),
        Expr::lam(
            BinderInfo::Default,
            bool_ty(),
            Expr::const_(Name::from_string("Bool.true"), vec![]),
        ),
    )
}

/// `ir_nat_pos n`, verbatim from `clean-verify`'s registered source. This is
/// what `ir_nat_ltb` runs, so it is the whole EvalIR comparison engine.
fn ir_nat_pos(n: Expr) -> Expr {
    Expr::apps(
        nat_rec(),
        [
            Expr::lam(BinderInfo::Default, nat_ty(), bool_ty()),
            Expr::const_(Name::from_string("Bool.false"), vec![]),
            ir_nat_pos_succ_minor(),
            n,
        ],
    )
}

/// **THE MINIMAL REPRO of `ir_nat_dbl_w`.**
///
/// `clean-verify` registers
/// `def ir_nat_dbl_w : Eq Nat (ir_nat_dbl 9007199254740991) 18014398509481982 :=
/// Eq.refl Nat 18014398509481982`, and that `Eq.refl` type-checks exactly when
/// this `is_def_eq` holds. Under `78d86fb51`'s guard the recursor is refused,
/// `whnf` returns the untouched `Nat.rec` application, and this fails.
#[test]
fn test_ir_nat_dbl_at_53_bits_reduces_in_one_iota_step() {
    let env = nat_bool_env();
    let tc = TypeChecker::new(&env);

    let lhs = ir_nat_dbl(Expr::nat_lit(TWO_POW_53_MINUS_1));
    let rhs = Expr::nat_lit(TWO_POW_54_MINUS_2);

    let reduced = tc.whnf(&lhs);
    assert!(
        matches!(&reduced.kind, ExprKind::Lit(Literal::Nat(n)) if *n == crate::expr::BigNat::Small(TWO_POW_54_MINUS_2)),
        "ir_nat_dbl (2^53-1) must whnf to the literal {TWO_POW_54_MINUS_2}; a recursor guard \
         keyed on the MAGNITUDE of the major leaves it stuck as {reduced:?}. This is the \
         `axiom_refutation_gate` failure that reverted 78d86fb51, in milliseconds."
    );
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "ir_nat_dbl_w's Eq.refl needs this def-eq to hold"
    );
}

/// The same requirement for the primitive `ir_nat_ltb` is built on, at the
/// EXACT major that explodes `import Init`.
///
/// This is the sharpest statement of why no threshold works: `2^32` must be
/// blocked in `Nat.decEq`'s tower and permitted here, in the same kernel, on
/// the same constructor, with the same literal.
#[test]
fn test_ir_nat_pos_at_the_import_trigger_major_still_decides() {
    let env = nat_bool_env();
    let tc = TypeChecker::new(&env);

    let e = ir_nat_pos(Expr::nat_lit(TWO_POW_32));
    let expected = Expr::const_(Name::from_string("Bool.true"), vec![]);

    let reduced = tc.whnf(&e);
    assert!(
        matches!(&reduced.kind, ExprKind::Const(n, _) if *n == Name::from_string("Bool.true")),
        "ir_nat_pos 2^32 must decide Bool.true on the FIRST iota step; got {reduced:?}. \
         ir_nat_ltb a b := ir_nat_pos (Nat.sub b a), so blocking this blocks every wide \
         comparison in the EvalIR substrate — ir_nat_bitlen, ir_dm_go, ir_nat_divmod, \
         ir_nat_mulb, ir_nat_min, ir_nat_max."
    );
    assert!(tc.is_def_eq(&e, &expected));
}

/// **The discriminator.** Both minors bind an induction hypothesis and never
/// mention it — that, not the major's magnitude, is what separates these from
/// `Nat.decEq`'s genuine 4.29-billion-step walk. A future guard that keys on
/// ih-usage passes this file; one that keys on a count cannot.
#[test]
fn test_the_wide_major_minors_discard_their_ih() {
    /// Does `BVar(depth)` occur in `e`, counting binders from here?
    fn mentions_bvar(e: &Expr, depth: u32) -> bool {
        match e.kind() {
            ExprKind::BVar(i) => *i == depth,
            ExprKind::App(f, a) => mentions_bvar(f, depth) || mentions_bvar(a, depth),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                mentions_bvar(ty, depth) || mentions_bvar(body, depth + 1)
            }
            _ => false,
        }
    }

    for (name, minor) in [
        ("ir_nat_dbl", ir_nat_dbl_succ_minor()),
        ("ir_nat_pos", ir_nat_pos_succ_minor()),
    ] {
        let ExprKind::Lam(_, _, inner) = minor.kind() else {
            panic!("{name}'s minor is a two-argument lambda");
        };
        let ExprKind::Lam(_, _, body) = inner.kind() else {
            panic!("{name}'s minor is a two-argument lambda");
        };
        assert!(
            !mentions_bvar(body, 0),
            "{name}'s successor minor must DISCARD its induction hypothesis — that is what \
             makes the recursor one step at any major, and it is the only property that \
             separates it from the Nat.decEq tower a fix has to stop."
        );
    }
}
