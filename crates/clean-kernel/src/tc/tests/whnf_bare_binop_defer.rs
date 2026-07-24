// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for the BARE guarded-binop eager-unfold deferral
//! (`try_unfold_definition`, whnf_proj.rs) — the bare-Const guard-bypass
//! closure.
//!
//! A bare `Nat.add`/`Nat.sub`/`Nat.mul`/`Nat.pow` Const exposed WITHOUT its
//! operands (typically an instance-projection FIELD extracted out of
//! `Mul.mk Nat.mul` while an application head is being whnf'd) must NOT be
//! eagerly delta-unfolded at the whnf outer-loop delta site: the caller
//! (`beta_or_iota_step`) would beta the raw recursor-seed lambda directly
//! into a materialized Θ(count) unary tower. Deferring lets the caller
//! re-form the full `Nat.mul a b` app, where `reduce_nat` accelerates the
//! closed case in binary and the existing `native_nat_binop_grind_stuck`
//! guard sticks the mixed large-count case (Lean parity:
//! type_checker.cpp:576-585, 604-633 — reduce_nat runs before
//! unfold_definition on every whnf iteration, and whnf_core never
//! delta-unfolds heads).
//!
//! The deferral is scoped to the outer-loop eager path ONLY: a direct
//! `whnf_core` of a bare guarded Const (the Full-mode Const arm) and
//! def-eq's lazy-delta unfolds are unchanged — both are pinned below.
//!
//! ALSO pinned here (same site, same lane): the APPLIED guarded-binop grind
//! guard at the outer-loop unfold COMMIT point. `whnf_core_inner`'s App arm
//! and def-eq's `get_delta_const` both leave a mixed-operand
//! `Nat.add a <closed count >= 512>` stuck via
//! `native_nat_binop_grind_stuck`, but `try_unfold_definition` used to
//! unfold the identical application unconditionally on every full
//! `whnf_impl`, overriding the core arm's verdict and walking the Θ(count)
//! recursor tower (the Init/GrindInstances/ToInt 2M-heartbeat residual —
//! live-traced `Nat.add fvar 2^31` launched from the `reduce_int` literal
//! extraction probes).

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::Declaration;

/// Env with the Nat recursor seeds plus a one-field structure
/// `MulHolder := ⟨Nat → Nat → Nat⟩` and a reducible instance
/// `instMulHolder : MulHolder := MulHolder.mk Nat.mul` — the minimal
/// replica of the `Mul Nat`/`OfNat` instance-projection shape behind the
/// Init/GrindInstances/ToInt omega frames.
fn mul_holder_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let holder = Name::from_string("MulHolder");
    let binop_ty = Expr::pi(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::pi(BinderInfo::Default, nat_ty.clone(), nat_ty),
    );
    let mk_type = Expr::pi(
        BinderInfo::Default,
        binop_ty,
        Expr::const_(holder.clone(), vec![]),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: holder.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("MulHolder.mk"),
                type_: mk_type,
            }],
        }],
    })
    .expect("MulHolder inductive should add");

    // instMulHolder := MulHolder.mk Nat.mul (test-env setup; unchecked add
    // follows the established tests/defeq.rs pattern).
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("instMulHolder"),
        level_params: vec![],
        type_: Expr::const_(holder, vec![]),
        value: Expr::app(
            Expr::const_(Name::from_string("MulHolder.mk"), vec![]),
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
        ),
        is_reducible: true,
    });

    env
}

/// `Proj(MulHolder, 0, instMulHolder)` — the extracted-field form.
fn holder_proj() -> Expr {
    Expr::proj(
        Name::from_string("MulHolder"),
        0,
        Expr::const_(Name::from_string("instMulHolder"), vec![]),
    )
}

/// The outer-loop eager path defers ALL FOUR guarded binops (whnf of the
/// bare Const is a fixpoint), while the general Const arm (`whnf_core`)
/// still unfolds them to their recursor-seed lambdas, and non-guarded
/// definitions are unaffected on both paths.
#[test]
fn test_whnf_bare_guarded_nat_binop_defers_at_outer_loop_only() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");

    // Non-guarded control: idnat := fun n : Nat => n.
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl_unchecked(Declaration::Definition {
        name: Name::from_string("idnat"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat_ty.clone(), nat_ty.clone()),
        value: Expr::lam(BinderInfo::Default, nat_ty, Expr::bvar(0)),
        is_reducible: true,
    });

    let tc = TypeChecker::new(&env);

    for op in ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow"] {
        let bare = Expr::const_(Name::from_string(op), vec![]);

        // Outer-loop eager path (whnf): DEFERRED — the bare op stays folded,
        // and the result is a whnf fixpoint (idempotency preserved).
        let w = tc.whnf(&bare);
        assert_eq!(w, bare, "whnf must keep bare {op} folded (deferral)");
        assert_eq!(
            tc.whnf(&w),
            w,
            "whnf of the deferred {op} must be a fixpoint"
        );

        // General Const arm (whnf_core, Full mode): UNCHANGED — a direct
        // core whnf of the bare op still exposes the recursor-seed lambda
        // (the user-facing "give me the lambda" demand).
        let core = tc.whnf_core(&bare);
        assert!(
            core.is_lam(),
            "whnf_core must still unfold bare {op} to its seed lambda"
        );
    }

    // Non-guarded definition: the outer-loop delta site is unaffected.
    let bare_id = Expr::const_(Name::from_string("idnat"), vec![]);
    assert!(
        tc.whnf(&bare_id).is_lam(),
        "whnf must still unfold a bare NON-guarded definition to its lambda"
    );
}

/// NON-VACUITY + acceleration replica of the ToInt fix: the
/// instance-projection field extraction exposes a bare `Nat.mul`, the
/// deferral keeps it folded, and the caller's rebuild re-forms the full
/// 2-arg app so `reduce_nat` computes the closed 2^31-scale case in binary
/// (instantly — the pre-fix path materializes a Θ(2^31) unary recursor
/// walk that can not fit any heartbeat).
#[test]
fn test_whnf_proj_field_bare_nat_binop_reforms_and_accelerates() {
    let env = mul_holder_env();
    let tc = TypeChecker::new(&env);

    // Non-vacuity: whnf of the standalone extracted field is the FOLDED
    // `Nat.mul` Const (pre-fix: the eagerly-unfolded seed lambda).
    let proj = holder_proj();
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);
    assert_eq!(
        tc.whnf(&proj),
        nat_mul,
        "proj-field whnf must return the folded Nat.mul (deferral fires)"
    );

    // Acceleration: (Proj(MulHolder,0,instMulHolder)) 2 2^31 — the big
    // literal sits in the RECURSION slot (2nd operand). The re-formed
    // `Nat.mul 2 2^31` must reduce in binary to 2^32.
    let app = Expr::app(
        Expr::app(holder_proj(), Expr::nat_lit(2)),
        Expr::nat_lit(2_147_483_648),
    );
    assert_eq!(
        tc.whnf(&app),
        Expr::nat_lit(4_294_967_296),
        "closed 2^31-scale binop through the proj field must reduce in binary"
    );
}

/// Verdict preservation: the deferral never changes what def-eq accepts —
/// the folded form, the explicitly-unfolded lambda, and the app-attached
/// unfold route all keep their verdicts.
#[test]
fn test_def_eq_bare_nat_binop_deferral_preserves_verdicts() {
    let env = mul_holder_env();
    let tc = TypeChecker::new(&env);

    let proj = holder_proj();
    let nat_mul = Expr::const_(Name::from_string("Nat.mul"), vec![]);

    // Folded-vs-folded: the extracted field IS Nat.mul.
    assert!(
        tc.is_def_eq(&proj, &nat_mul),
        "proj field must stay def-eq to the folded Nat.mul"
    );

    // Folded-vs-unfolded: def-eq must still unfold the bare op when
    // demanded (lazy delta / the Const arm) — deferral defers, never blocks.
    let seed_lambda = tc.whnf_core(&nat_mul);
    assert!(
        seed_lambda.is_lam(),
        "whnf_core must expose the Nat.mul seed lambda"
    );
    assert!(
        tc.is_def_eq(&proj, &seed_lambda),
        "proj field must stay def-eq to the unfolded Nat.mul seed lambda"
    );

    // Mixed-operand app through the proj route: the app-attached unfold
    // semantics are unchanged (small counts still converge, unequal counts
    // still differ).
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let x_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("x"), nat_ty, BinderInfo::Default);
    let x = Expr::fvar(x_id);
    let via_proj = Expr::app(Expr::app(holder_proj(), x.clone()), Expr::nat_lit(3));
    let direct =
        |count: u64| Expr::app(Expr::app(nat_mul.clone(), x.clone()), Expr::nat_lit(count));
    assert!(
        tc.is_def_eq(&via_proj, &direct(3)),
        "proj-routed mixed app must stay def-eq to the direct Nat.mul app"
    );
    assert!(
        !tc.is_def_eq(&via_proj, &direct(4)),
        "unequal recursion counts must stay NOT def-eq through the proj route"
    );
}

/// APPLIED commit-point guard: a mixed-operand guarded binop with a LARGE
/// closed recursion count must stay STUCK through a full `whnf` (the outer
/// loop's `try_unfold_definition` no longer overrides the core App-arm
/// guard), while SMALL counts still unfold and reduce (completeness
/// preserved — the guard threshold is untouched).
#[test]
fn test_whnf_applied_mixed_guarded_binop_large_count_stays_stuck() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let tc = TypeChecker::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let x_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("x"), nat_ty, BinderInfo::Default);
    let x = Expr::fvar(x_id);

    for op in ["Nat.add", "Nat.sub", "Nat.mul", "Nat.pow"] {
        // The live-traced residual shape: `<op> fvar 2^31`.
        let app = Expr::app(
            Expr::app(Expr::const_(Name::from_string(op), vec![]), x.clone()),
            Expr::nat_lit(2_147_483_648),
        );
        let w = tc.whnf(&app);
        assert_eq!(
            w, app,
            "whnf must leave the mixed large-count {op} app STUCK (commit-point guard)"
        );
        assert_eq!(tc.whnf(&w), w, "the stuck {op} app must be a whnf fixpoint");
    }

    // Small-count control: the guard threshold (512) is untouched — a small
    // mixed count still unfolds and iota-reduces to a successor tower.
    let small = Expr::app(
        Expr::app(Expr::const_(Name::from_string("Nat.add"), vec![]), x),
        Expr::nat_lit(3),
    );
    let w = tc.whnf(&small);
    assert_ne!(
        w, small,
        "small mixed counts must still unfold (completeness)"
    );
    assert!(
        TypeChecker::is_nat_succ_expr(&w).is_some(),
        "whnf of `Nat.add x 3` must expose its leading successor"
    );
}

/// Closed-closed applications never reach the commit-point guard:
/// `reduce_nat` computes them in binary one stage earlier in the SAME outer
/// loop, at full 2^31 scale.
#[test]
fn test_whnf_applied_closed_guarded_binop_still_accelerates_in_binary() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let tc = TypeChecker::new(&env);

    let big = 2_147_483_648u64; // 2^31
    let add = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.add"), vec![]),
            Expr::nat_lit(big),
        ),
        Expr::nat_lit(big),
    );
    assert_eq!(
        tc.whnf(&add),
        Expr::nat_lit(4_294_967_296),
        "closed 2^31 + 2^31 must reduce in binary through full whnf"
    );

    let mul = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Nat.mul"), vec![]),
            Expr::nat_lit(2),
        ),
        Expr::nat_lit(big),
    );
    assert_eq!(
        tc.whnf(&mul),
        Expr::nat_lit(4_294_967_296),
        "closed 2 * 2^31 must reduce in binary through full whnf"
    );
}

/// Verdict preservation across the stuck form: def-eq on guarded-stuck apps
/// keeps its verdicts — congruence closes equal pairs, unequal counts stay
/// rejected, and the one-layer succ reconciliation (`nat_add_succ_pred`)
/// still fires against a genuine successor.
#[test]
fn test_def_eq_applied_guarded_binop_stuck_preserves_verdicts() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let tc = TypeChecker::new(&env);

    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let x_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("x"), nat_ty, BinderInfo::Default);
    let x = Expr::fvar(x_id);
    let add = |count: u64| {
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Nat.add"), vec![]),
                x.clone(),
            ),
            Expr::nat_lit(count),
        )
    };

    let big = 2_147_483_648u64; // 2^31
    assert!(
        tc.is_def_eq(&add(big), &add(big)),
        "stuck-vs-stuck congruence must accept the equal pair"
    );
    assert!(
        !tc.is_def_eq(&add(big), &add(big + 1)),
        "unequal large counts must stay NOT def-eq"
    );
    // One hidden successor: `Nat.succ (Nat.add x (big-1))` IS `Nat.add x big`.
    let succ_of_pred = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        add(big - 1),
    );
    assert!(
        tc.is_def_eq(&succ_of_pred, &add(big)),
        "the offset succ-reconciliation must still close succ(add x (n-1)) = add x n"
    );
}
