// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for #3528: `rfl` fails to close
//! `Prod.casesOn (Prod.mk a b) motive minor = Prod.casesOn (Prod.mk c d) motive minor`
//! where iota-reduction of both sides yields the same constant result.
//!
//! The minimal failing pattern from tMIR#29:
//! ```lean
//! theorem myLand_comm (a b : Int) : myLand a b = myLand b a := by
//!   ... cases a with
//!   | ofNat m => cases b with
//!     | negSucc n => rfl  -- FAILS: both reduce to Int.ofNat 0 via fallthrough
//! ```

use super::*;
use clean_kernel::expr::BinderInfo;
use clean_kernel::level::Level;

/// Build a fresh environment populated with Int, Prod, Eq, Nat.
fn setup_env_with_int_prod() -> Environment {
    let mut env = Environment::new();
    env.init_nat().unwrap();
    env.init_eq().unwrap();
    env.init_prod().unwrap();
    env.init_int().unwrap();
    env
}

/// Helper: build `@Eq.{1} Int lhs rhs`.
fn int_eq_goal(lhs: Expr, rhs: Expr) -> Expr {
    let int = int_ty();
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                int,
            ),
            lhs,
        ),
        rhs,
    )
}

fn int_ty() -> Expr {
    Expr::const_(Name::from_string("Int"), vec![])
}

fn nat_ty() -> Expr {
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn nat_zero() -> Expr {
    Expr::const_(Name::from_string("Nat.zero"), vec![])
}

/// Build `Int.ofNat 0`.
fn int_zero() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.ofNat"), vec![]),
        nat_zero(),
    )
}

fn int_ofnat_0() -> Expr {
    int_zero()
}

fn int_negsucc_0() -> Expr {
    Expr::app(
        Expr::const_(Name::from_string("Int.negSucc"), vec![]),
        nat_zero(),
    )
}

/// Build `Prod.{u,v} α β`.
fn prod_apply(alpha: &Expr, beta: &Expr, u: Level, v: Level) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Prod"), vec![u, v]),
            alpha.clone(),
        ),
        beta.clone(),
    )
}

/// Build `Prod.mk {α} {β} a b`.
fn prod_mk(alpha: &Expr, beta: &Expr, a: &Expr, b: &Expr, u: Level, v: Level) -> Expr {
    let mk = Expr::const_(Name::from_string("Prod.mk"), vec![u, v]);
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(mk, alpha.clone()), beta.clone()),
            a.clone(),
        ),
        b.clone(),
    )
}

/// Build `Prod.casesOn.{u_motive, u, v} {α} {β} motive major minor`.
///
/// Argument order: clean's recursor builder emits casesOn with the
/// Lean-faithful `RecursorArgOrder::MajorAfterMotive`, so the major premise
/// precedes the minor. Signature:
///   Prod.casesOn : {α : Type u} → {β : Type v} → {motive : Prod α β → Sort u_motive}
///                → (t : Prod α β)
///                → (minor : α → β → motive (Prod.mk α β a b)) → motive t
fn prod_cases_on(
    alpha: &Expr,
    beta: &Expr,
    motive: &Expr,
    minor: &Expr,
    major: &Expr,
    u_motive: Level,
    u: Level,
    v: Level,
) -> Expr {
    let c = Expr::const_(Name::from_string("Prod.casesOn"), vec![u_motive, u, v]);
    Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(c, alpha.clone()), beta.clone()),
                motive.clone(),
            ),
            major.clone(),
        ),
        minor.clone(),
    )
}

/// `fun (_ : Int) (_ : Int) => Int.ofNat 0`.
fn int_int_const_zero_minor() -> Expr {
    let int = int_ty();
    Expr::lam(
        BinderInfo::Default,
        int.clone(),
        Expr::lam(BinderInfo::Default, int, int_zero()),
    )
}

/// `fun (_ : Prod Int Int) => Int`.
fn prod_int_int_to_int_motive() -> Expr {
    let int = int_ty();
    let prod_int_int = prod_apply(&int, &int, Level::zero(), Level::zero());
    Expr::lam(BinderInfo::Default, prod_int_int, int)
}

/// Build `Prod.casesOn (Prod.mk a b) (fun _ _ => Int.ofNat 0)` on `Int × Int`.
fn prod_cases_on_int_int_const_zero(a: &Expr, b: &Expr) -> Expr {
    let int = int_ty();
    let u = Level::zero();
    let v = Level::zero();
    let u_motive = Level::succ(Level::zero());
    prod_cases_on(
        &int,
        &int,
        &prod_int_int_to_int_motive(),
        &int_int_const_zero_minor(),
        &prod_mk(&int, &int, a, b, u.clone(), v.clone()),
        u_motive,
        u,
        v,
    )
}

/// Minimal regression for #3528:
///
/// The cross-branch `rfl` after `cases a with | ofNat m => cases b with | negSucc n`
/// presents a goal of the shape:
///   `Prod.casesOn (Prod.mk (Int.ofNat m) (Int.negSucc n)) (fun _ _ => 0)
///  = Prod.casesOn (Prod.mk (Int.negSucc n) (Int.ofNat m)) (fun _ _ => 0)`
///
/// Both sides iota-reduce to `Int.ofNat 0`, so `rfl` must succeed.
#[test]
fn test_rfl_prod_cases_on_fallthrough_identical_minor() {
    let env = setup_env_with_int_prod();
    let lhs = prod_cases_on_int_int_const_zero(&int_ofnat_0(), &int_negsucc_0());
    let rhs = prod_cases_on_int_int_const_zero(&int_negsucc_0(), &int_ofnat_0());
    let goal = int_eq_goal(lhs, rhs);

    let mut state = ProofState::new(env, goal);
    rfl(&mut state).expect(
        "rfl should close Prod.casesOn (mk a b) (fun _ _ => 0) = Prod.casesOn (mk c d) (fun _ _ => 0) \
         — both iota-reduce to Int.ofNat 0 (regression for #3528)",
    );
    assert!(
        state.is_complete(),
        "rfl should fully close the goal (regression for #3528)"
    );
}

// ---------------------------------------------------------------------------
// Deeper #3528 reproduction: outer-beta + nested Int.casesOn reduction chain.
// ---------------------------------------------------------------------------

/// `Int.casesOn (fun _ => Int) of_nat_arm neg_succ_arm major` with given arms.
fn int_cases_on(of_nat_arm: Expr, neg_succ_arm: Expr, major: Expr) -> Expr {
    let u_motive = Level::succ(Level::zero());
    let int_cases_on_const = Expr::const_(Name::from_string("Int.casesOn"), vec![u_motive]);
    let int_motive = Expr::lam(BinderInfo::Default, int_ty(), int_ty());
    Expr::app(
        Expr::app(
            Expr::app(Expr::app(int_cases_on_const, int_motive), of_nat_arm),
            neg_succ_arm,
        ),
        major,
    )
}

/// `fun (_ : Nat) => body`.
fn nat_lam(body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, nat_ty(), body)
}

/// `(fun _ : Int _ : Int => Int.ofNat 0) BVar(i) BVar(j)` — the fallthrough
/// redex generated by match-compilation applied to outer-bound variables.
fn fallthrough_redex(i: u32, j: u32) -> Expr {
    let lam = int_int_const_zero_minor();
    Expr::app(Expr::app(lam, Expr::bvar(i)), Expr::bvar(j))
}

/// Build the `myLand` match-compiled Prod.casesOn minor:
/// `fun (a : Int) (b : Int) => Int.casesOn_a (ofNat_a => Int.casesOn_b (...)) (negSucc_a => ...)`.
fn myland_match_compiled_minor() -> Expr {
    let int = int_ty();
    // Inner Int.casesOn on b (under outer ofNat_m arm): both arms reduce to
    // Int.ofNat 0 (fallthrough redex for negSucc_n).
    let inner_on_b = int_cases_on(
        nat_lam(int_zero()),              // ofNat n arm
        nat_lam(fallthrough_redex(3, 2)), // negSucc n arm (fallthrough)
        Expr::bvar(0),                    // major = outer `b`
    );
    // Outer Int.casesOn on a: ofNat_m arm calls inner_on_b; negSucc_m arm
    // is the outer fallthrough redex.
    let outer_on_a = int_cases_on(
        nat_lam(inner_on_b),              // ofNat m arm
        nat_lam(fallthrough_redex(2, 1)), // negSucc m arm (fallthrough)
        Expr::bvar(1),                    // major = outer `a`
    );
    Expr::lam(
        BinderInfo::Default,
        int.clone(),
        Expr::lam(BinderInfo::Default, int, outer_on_a),
    )
}

/// Build the outer-beta wrapper around `Prod.casesOn`:
/// `fun (a : Int) (b : Int) => Prod.casesOn motive minor (Prod.mk a b)`.
fn myland_outer_beta_lambda() -> Expr {
    let int = int_ty();
    let u = Level::zero();
    let v = Level::zero();
    let u_motive = Level::succ(Level::zero());
    let body = prod_cases_on(
        &int,
        &int,
        &prod_int_int_to_int_motive(),
        &myland_match_compiled_minor(),
        &prod_mk(
            &int,
            &int,
            &Expr::bvar(1),
            &Expr::bvar(0),
            u.clone(),
            v.clone(),
        ),
        u_motive,
        u,
        v,
    );
    Expr::lam(
        BinderInfo::Default,
        int.clone(),
        Expr::lam(BinderInfo::Default, int, body),
    )
}

/// Deeper reproduction of #3528 covering the full match-compiled
/// `myLand_comm` shape. This pins the currently-broken deeper WHNF
/// reduction chain as a negative regression: if either the kernel
/// `is_def_eq` or `rfl` ever succeed on this goal, the deeper fix has
/// landed and the assertions should be flipped.
#[test]
fn test_rfl_unfold_myland_comm_fallthrough_deeper_whnf_limitation() {
    let env = setup_env_with_int_prod();
    let outer = myland_outer_beta_lambda();
    let lhs = Expr::app(Expr::app(outer.clone(), int_ofnat_0()), int_negsucc_0());
    let rhs = Expr::app(Expr::app(outer, int_negsucc_0()), int_ofnat_0());
    let goal = int_eq_goal(lhs.clone(), rhs.clone());

    // Kernel does not push outer-beta through nested casesOn on BVar majors today.
    let kernel_def_eq = {
        let tc = TypeChecker::new(&env);
        tc.is_def_eq(&lhs, &rhs)
    };
    assert!(
        !kernel_def_eq,
        "FOLLOW-UP for #3528: deeper WHNF reduction through outer-beta + \
         nested casesOn is expected to fail today. If this now returns true, \
         flip the assertion and close the follow-up."
    );

    let mut state = ProofState::new(env, goal);
    let rfl_result = rfl(&mut state);
    assert!(
        rfl_result.is_err() || !state.is_complete(),
        "FOLLOW-UP for #3528: rfl on outer-beta + nested casesOn is expected \
         to fail today. If this now succeeds, flip the assertion and close \
         the follow-up."
    );
}
