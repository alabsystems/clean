// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `interval_cases` interval-descent tests (#2480, #2533).
//!
//! Split out of `finite_cases_proof_chain.rs` (file-size rule). That file keeps
//! the `build_or_elim_chain` structural tests — the `fin_cases` path, which
//! `interval_cases` no longer routes through — plus the bound/range error paths
//! and `expr_to_int`. This file owns everything that exercises the descent
//! itself.
//!
//! The load-bearing test is
//! `test_interval_cases_branches_consume_n_eq_and_close_proof`: it USES each
//! branch equality and then demands a fully closed proof term, so a "fix" that
//! merely silenced the goal-scope guard cannot pass it.

use super::*;
use clean_kernel::env::Declaration;
use clean_kernel::expr::ExprKind;
use clean_kernel::{BinderInfo, Level};

/// Build `@LT.lt.{0} Nat instLTNat lhs rhs`.
/// Mirrors `make_nat_le_tc` but for strict inequality.
pub(super) fn make_nat_lt_tc(lhs: Expr, rhs: Expr) -> Expr {
    tc_app::nat_lt_tc(lhs, rhs)
}

/// The `SurfaceName` a test local (or a tactic-generated one, `n_eq`) carries.
pub(super) fn sname(name: &str) -> clean_parser::SurfaceName {
    clean_parser::SurfaceName::generated_path(name)
}

/// Full Nat order theory for the `interval_cases` interval descent.
///
/// The descent cites `Nat.lt_or_eq_of_le`, `Nat.le_of_succ_le_succ`,
/// `Nat.le_trans`, `Nat.lt_irrefl` and `False.elim`. `Environment::with_prelude`
/// is the only `pub` door to that set: `init_nat_lt_or_eq_of_le`
/// (`order_lemmas.rs`) and `init_nat_totality_proofs` (`nat_totality_proof.rs`)
/// are `pub(crate)` inside clean-kernel, and promoting them would raise
/// `paragon_ratchet.sh`'s `bare_pub_non_lib` count. Going through the prelude
/// means every lemma the tactic cites is the GENUINE constructive
/// `Declaration::Theorem`, not a fixture axiom.
pub(super) fn setup_env_for_interval_cases_ordered() -> Environment {
    let mut env = Environment::with_prelude();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("R"),
        level_params: vec![],
        type_: Expr::arrow(nat_ty, Expr::prop()),
    })
    .expect("R : Nat → Prop should register");

    // Witnesses `r_k : R k`, used by the tests that CONSUME `n_eq`.
    for k in 0..=5u64 {
        env.add_decl(Declaration::Axiom {
            name: Name::from_string(&format!("r{k}")),
            level_params: vec![],
            type_: Expr::app(
                Expr::const_(Name::from_string("R"), vec![]),
                make_nat_literal(k),
            ),
        })
        .expect("r_k : R k should register");
    }

    env
}

// =========================================================================
// #2480 regression coverage: dependent targets keep the original target
// =========================================================================

/// Regression for #2480: dependent interval goals now keep their original
/// target and rely on the generated equality hypothesis for case refinement.
#[test]
fn test_interval_cases_dependent_target_succeeds() {
    // CONTRACT CORRECTION (not a weakening): the ENVIRONMENT changes, from a
    // fixture that contained no `LE`, no `LT`, no `Nat.le` and no Nat order
    // lemma at all, to one that does. `interval_cases` now DERIVES each
    // branch's `n = v` from `Nat.lt_or_eq_of_le` instead of asserting it at an
    // out-of-band FVar, so it legitimately needs the lemmas it cites. Supplying
    // them is providing the tactic's stated environment precondition; every
    // claim this test makes (`is_ok`, 3 sub-goals, preserved target, `n_eq`
    // present) is still checked, and `n_eq` is now backed by a real binder over
    // a real proof.
    //
    // An interim `Or.rec`/`Classical.em` fix asserted the opposite for the LAST
    // branch ("only branches backed by an equality lambda may carry n_eq"),
    // because that chain had no proof of `n = hi` and so withheld it. The
    // descent proves it, so EVERY branch carries `n_eq`, and this test pins its
    // exact statement per branch; the consumption test below then USES each
    // one inside a kernel-checked closed proof.
    let env = setup_env_for_interval_cases_ordered();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    // Goal: R(n) where n : Nat, with 2 ≤ n and n ≤ 4 in context.
    //
    // Built through `with_context` so the root metavariable is minted holding
    // exactly this obligation. `ProofState::new(env, Expr::prop())` plus
    // post-hoc `goals[0].target = ...` / `local_ctx.push(...)` leaves the
    // metavariable at `⊢ Prop` over an empty scope, and `close_goal` correctly
    // refuses to let the mutated Goal stand in for it. (`interval_state` below
    // covers the `with_elab_context` layout, where these locals sit below
    // `fvar_base`; here they are tactic-scope ids 0..=2.)
    let n_fvar = FVarId::new(0);
    let h_lower_fvar = FVarId::new(1);
    let h_upper_fvar = FVarId::new(2);
    let target = Expr::app(r_const.clone(), Expr::fvar(n_fvar));
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: n_fvar,
                name: sname("n"),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: h_lower_fvar,
                name: sname("h_lower"),
                ty: make_nat_le_tc(make_nat_literal(2), Expr::fvar(n_fvar)),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: h_upper_fvar,
                name: sname("h_upper"),
                ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(4)),
                value: None,
            },
        ],
    );

    let result = interval_cases(&mut state, &sname("n"));
    assert!(
        result.is_ok(),
        "interval_cases with dependent target should succeed, got: {result:?}"
    );
    assert_eq!(
        state.goals.len(),
        3,
        "interval_cases should create 3 sub-goals"
    );
    // Goals are in ascending value order: 2, 3, 4.
    for (goal, value) in state.goals.iter().zip(2u64..) {
        assert_eq!(
            goal.target, target,
            "dependent interval sub-goals should preserve the original target"
        );
        let n_eq = goal
            .local_ctx
            .iter()
            .find(|decl| decl.name == sname("n_eq"))
            .unwrap_or_else(|| panic!("sub-goal {value} should carry the generated n_eq"));
        assert_eq!(
            n_eq.ty,
            make_equality_type(
                &nat_ty,
                &Expr::fvar(n_fvar),
                &make_nat_literal(value),
                Level::succ(Level::zero()),
            ),
            "branch {value}'s n_eq must state `n = {value}`, the last branch included"
        );
    }
}

/// Same regression for LT bounds: 1 < n < 5 with dependent target R(n).
#[test]
fn test_interval_cases_lt_dependent_target_succeeds() {
    // CONTRACT CORRECTION (not a weakening): environment, and `n_eq` on EVERY
    // branch — see `test_interval_cases_dependent_target_succeeds`.
    let env = setup_env_for_interval_cases_ordered();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    // Real obligation up front — see `test_interval_cases_dependent_target_succeeds`.
    let n_fvar = FVarId::new(0);
    let h_lower_fvar = FVarId::new(1);
    let h_upper_fvar = FVarId::new(2);
    let target = Expr::app(r_const, Expr::fvar(n_fvar));
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: n_fvar,
                name: sname("n"),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: h_lower_fvar,
                name: sname("h_lower"),
                ty: make_nat_lt_tc(make_nat_literal(1), Expr::fvar(n_fvar)),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: h_upper_fvar,
                name: sname("h_upper"),
                ty: make_nat_lt_tc(Expr::fvar(n_fvar), make_nat_literal(5)),
                value: None,
            },
        ],
    );

    let result = interval_cases(&mut state, &sname("n"));
    assert!(
        result.is_ok(),
        "interval_cases LT with dependent target should succeed, got: {result:?}"
    );
    assert_eq!(
        state.goals.len(),
        3,
        "strict interval should create 3 sub-goals"
    );
    for goal in &state.goals {
        assert_eq!(goal.target, target);
        assert!(goal.local_ctx.iter().any(|decl| decl.name == sname("n_eq")));
    }
}

/// Single-value intervals also stay type-correct for dependent targets.
#[test]
fn test_interval_cases_single_value_dependent_target_succeeds() {
    // CONTRACT CORRECTION (not a weakening): environment, and `n_eq` on EVERY
    // branch — see `test_interval_cases_dependent_target_succeeds`.
    // `lo == hi` is the ORDINARY `idx == 0` rung of the descent, not a special
    // case: its `n_eq` binder is real and its `n < 3` escape is discharged
    // against `h_lower`.
    let env = setup_env_for_interval_cases_ordered();
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let r_const = Expr::const_(Name::from_string("R"), vec![]);

    // Real obligation up front — see `test_interval_cases_dependent_target_succeeds`.
    let n_fvar = FVarId::new(0);
    let h_lower_fvar = FVarId::new(1);
    let h_upper_fvar = FVarId::new(2);
    let target = Expr::app(r_const, Expr::fvar(n_fvar));
    let mut state = ProofState::with_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: n_fvar,
                name: sname("n"),
                ty: nat_ty.clone(),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: h_lower_fvar,
                name: sname("h_lower"),
                ty: make_nat_le_tc(make_nat_literal(3), Expr::fvar(n_fvar)),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: h_upper_fvar,
                name: sname("h_upper"),
                ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(3)),
                value: None,
            },
        ],
    );

    let result = interval_cases(&mut state, &sname("n"));
    assert!(
        result.is_ok(),
        "single-value interval_cases with dependent target should succeed, got: {result:?}"
    );
    assert_eq!(state.goals.len(), 1);
    assert_eq!(state.goals[0].target, target);
    assert!(state.goals[0]
        .local_ctx
        .iter()
        .any(|decl| decl.name == sname("n_eq")));
}

// =========================================================================
// #2533 regression coverage: the branch equality must be DERIVED, not assumed
// =========================================================================

/// Build a proof state for `⊢ R n` under `lo ≤ n` / `n ≤ hi` (non-strict).
///
/// Elaborator locals are `n@0`, `h_lower@1`, `h_upper@2`, so `fvar_base == 3`
/// and the descent's binder slots start at `FVarId(3)`.
pub(super) fn interval_state(env: Environment, lo: u64, hi: u64) -> (ProofState, Expr) {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let r_const = Expr::const_(Name::from_string("R"), vec![]);
    let n_fvar = FVarId::new(0);
    let target = Expr::app(r_const, Expr::fvar(n_fvar));
    let state = ProofState::with_elab_context(
        env,
        target.clone(),
        vec![
            LocalDecl {
                binder_info: Default::default(),
                fvar: n_fvar,
                name: sname("n"),
                ty: nat_ty,
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(1),
                name: sname("h_lower"),
                ty: make_nat_le_tc(make_nat_literal(lo), Expr::fvar(n_fvar)),
                value: None,
            },
            LocalDecl {
                binder_info: Default::default(),
                fvar: FVarId::new(2),
                name: sname("h_upper"),
                ty: make_nat_le_tc(Expr::fvar(n_fvar), make_nat_literal(hi)),
                value: None,
            },
        ],
    );
    (state, target)
}

/// `@Eq.ndrec.{0,1} Nat v (fun x : Nat => R x) r_v n (@Eq.symm.{1} Nat n v n_eq) : R n`
///
/// This is the operation `omega_tactic/case_split.rs` documented as impossible
/// on the old `interval_cases` proof: it CONSUMES the branch equality.
fn transport_r_along_n_eq(n: &Expr, value: u64, n_eq: &Expr) -> Expr {
    let nat_ty = Expr::const_(Name::from_string("Nat"), vec![]);
    let v = make_nat_literal(value);
    let motive = Expr::lam(
        BinderInfo::Default,
        nat_ty.clone(),
        Expr::app(Expr::const_(Name::from_string("R"), vec![]), Expr::bvar(0)),
    );
    // Eq.symm : ∀ {α : Sort u} {a b : α}, a = b → b = a  (α = Nat : Sort 1)
    let sym = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.symm"),
            vec![Level::succ(Level::zero())],
        ),
        [nat_ty.clone(), n.clone(), v.clone(), n_eq.clone()],
    );
    // Eq.ndrec levels are [motive-sort, carrier-sort] = [0, 1].
    Expr::apps(
        Expr::const_(
            Name::from_string("Eq.ndrec"),
            vec![Level::zero(), Level::succ(Level::zero())],
        ),
        [
            nat_ty,
            v,
            motive,
            Expr::const_(Name::from_string(&format!("r{value}")), vec![]),
            n.clone(),
            sym,
        ],
    )
}

/// Close every sub-goal by USING its `n_eq`, in ascending value order.
fn close_branches_using_n_eq(state: &mut ProofState, values: std::ops::RangeInclusive<u64>) {
    let n = Expr::fvar(FVarId::new(0));
    for value in values {
        let goal = state
            .current_goal()
            .cloned()
            .unwrap_or_else(|| panic!("sub-goal for value {value} should be open"));
        let n_eq = goal
            .local_ctx
            .iter()
            .find(|d| d.name == sname("n_eq"))
            .unwrap_or_else(|| panic!("sub-goal for value {value} should carry n_eq"))
            .clone();
        let proof = transport_r_along_n_eq(&n, value, &Expr::fvar(n_eq.fvar));
        state.close_goal(&goal, proof).unwrap_or_else(|err| {
            panic!("branch {value} should close by consuming n_eq, got: {err:?}")
        });
    }
}

/// THE test that pins the defect: each branch CONSUMES its `n_eq`, and the
/// assembled term then closes into a genuine proof of the original goal.
///
/// The old chain deferred its failure here: branch `k`'s own `close_goal`
/// permitted the out-of-band `FVarId(1003)` (it was in that meta's recorded
/// scope), and only `closed_proof`'s fail-closed FVar→BVar scan rejected the
/// result. A fix that merely relaxed the assignment guard would still fail
/// this test.
#[test]
fn test_interval_cases_branches_consume_n_eq_and_close_proof() {
    let env = setup_env_for_interval_cases_ordered();
    let (mut state, target) = interval_state(env, 2, 4);
    let root_goal = state
        .current_goal()
        .cloned()
        .expect("root goal should be open");

    interval_cases(&mut state, &sname("n")).expect("interval_cases 2 ≤ n ≤ 4 should succeed");
    assert_eq!(state.goals.len(), 3);

    close_branches_using_n_eq(&mut state, 2..=4);
    assert!(state.goals.is_empty(), "all branches should be closed");

    let closed = state
        .closed_proof()
        .expect("the assembled interval proof must close (no FVar→BVar gap)");
    assert!(
        !matches!(closed.kind(), ExprKind::FVar(_)),
        "closed interval proof should be an Or.rec descent, not a bare meta: {closed:?}"
    );
    let cert = state.verify_proof(&root_goal, &closed);
    assert!(
        cert.is_ok(),
        "closed interval proof should kernel-check at {target:?}, got: {cert:?}"
    );
}

/// `lo == hi` is the ordinary innermost rung, so its `n_eq` is equally usable.
#[test]
fn test_interval_cases_single_value_consumes_n_eq() {
    let env = setup_env_for_interval_cases_ordered();
    let (mut state, _target) = interval_state(env, 3, 3);
    let root_goal = state
        .current_goal()
        .cloned()
        .expect("root goal should be open");

    interval_cases(&mut state, &sname("n")).expect("interval_cases 3 ≤ n ≤ 3 should succeed");
    assert_eq!(state.goals.len(), 1);

    close_branches_using_n_eq(&mut state, 3..=3);

    let closed = state
        .closed_proof()
        .expect("single-value interval proof must close");
    let _ = state
        .verify_proof(&root_goal, &closed)
        .expect("single-value interval proof should kernel-check");
}
