// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! PKG4: the level-assignment funnel's occurs check, end to end.
//!
//! `theorem q {β : Sort _} {F G : β → β} (h : F = G) : ∀ x, F x = G x :=
//! congrFun h` did not TERMINATE: measured on main's frozen release binary
//! (`clean-5e2e6dc0e check`, this one-line file, no import) the process passed
//! 2 GB within seconds and was killed by a memory guard. `Eq.{?b} =?=
//! Eq.{imax ?u ?v}` solved `?b := imax ?u ?v`; `solve_head_const_levels` then
//! read `β : Sort ?b` against `congrFun`'s `{α : Sort ?u}` and stored
//! `?u := imax ?u ?v` through `MetaState::add_level_constraint` directly,
//! bypassing the occurs check `solve_level_eq` makes before it calls in. Every
//! later equation re-expanded the cyclic class under `stack_safe`, which grows
//! the stack instead of overflowing it — so the recursion ate memory, not
//! stack. The funnel now refuses a self-referential assignment, as Lean's
//! `isLevelDefEqAux` does (`!u.occurs v`, `Lean/Meta/LevelDefEq.lean`).
//!
//! MUTATION-CHECKED on this branch: with the funnel's check disabled the
//! fixture below passed 2.5 GB and was killed; with it, it finishes in
//! seconds.

use crate::tests_pkg4_unifier::{assert_elaborates, elab_after};
use crate::unify::MetaState;
use clean_kernel::name::Name;
use clean_kernel::Level;

/// The fixture does not terminate when the funnel accepts a cyclic level
/// assignment, and a non-terminating test here is a MEMORY hazard for the box,
/// not a red row. So the arm below first checks the property that makes the
/// fixture safe to run, and refuses to run it otherwise.
fn assert_funnel_refuses_cycle_before_running_fixture() {
    let mut metas = MetaState::new();
    let u = Level::param(Name::from_string("occ_u"));
    let v = Level::param(Name::from_string("occ_v"));
    assert!(
        metas
            .add_level_constraint(Name::from_string("occ_u"), Level::imax(u, v))
            .is_err(),
        "the level funnel accepted `?u := imax ?u ?v`; NOT running the congrFun fixture, \
         which does not terminate (and exhausts memory) without that refusal"
    );
}

/// CONTROL: two distinct `Sort _` binders never posed the cyclic equation and
/// elaborated on main all along. Pinned Lean accepts it.
#[test]
fn test_level_occurs_congr_fun_over_two_sort_holes_control_elaborates() {
    assert_funnel_refuses_cycle_before_running_fixture();
    assert_elaborates(
        "",
        "theorem q2 {α β : Sort _} {F G : α → β} (h : F = G) : ∀ x, F x = G x := congrFun h\n",
        "`congrFun h` over two `Sort _` binders",
    );
}

/// The non-terminating face now TERMINATES, fail-closed. Pinned Lean ACCEPTS
/// this declaration, so what is pinned here is an OPEN gap with its target:
/// Lean never meets `?b =?= imax ?u ?v` with `β : Sort ?b` still a
/// metavariable, because `levelMVarToParamHeaders`
/// (`Lean/Elab/MutualDef.lean`) turns a theorem header's universe
/// metavariables into parameters before the body is elaborated — a separate
/// root cause (rigid `Sort _` headers), not this package's. The day that
/// lands this arm fails at the `expect`, loudly: replace it with
/// `assert_elaborates`.
#[test]
fn test_level_occurs_congr_fun_over_one_sort_hole_terminates_fail_closed() {
    assert_funnel_refuses_cycle_before_running_fixture();
    let refusal = elab_after(
        "",
        "theorem q {β : Sort _} {F G : β → β} (h : F = G) : ∀ x, F x = G x := congrFun h\n",
    )
    .expect(
        "OPEN gap CLOSED: `congrFun h` over one `Sort _` binder now elaborates, as on pinned \
         Lean — replace this refusal pin with `assert_elaborates`",
    );
    assert!(
        refusal.contains("unresolved universe level equation after postponement"),
        "the refusal must be the level drain's fail-closed report, got: {refusal}"
    );
}

/// The ETA-EXPANDED face of the same OPEN gap — and the one face of it that
/// MOVED the other way, so it is pinned with its history rather than left to
/// be rediscovered as a ratchet surprise.
///
/// Main's frozen release binary (`clean-5e2e6dc0e`) reports `fun x => congrFun
/// h x` over ONE `Sort _` carrier as PASSED, where the direct `congrFun h`
/// above ran away in memory. That pass was the silent monomorphization the
/// `Sort ?u` binder repair exists to stop: the body is first elaborated with
/// no expected type (`try_elab_def_value_without_expected`), the unannotated
/// `fun x` binder was minted `?T : Type`, and `?T := β` pinned the header's
/// `Sort ?b` to `Sort 1` before `congrFun` could pose a symbolic level
/// equation. Measured on that binary: the registered theorem is `β : Type`
/// only — a use at `p : Prop` fails `universe level conflict: 0 vs 1`, a use
/// at `Type → Type` fails `1 vs 0`, and pinned Lean accepts both uses.
///
/// With the binder at `Sort ?u` nothing pins `?b`, the symbolic equations
/// `?u =?= imax ?u ?v` reach the level solver, and the declaration fails
/// CLOSED exactly like the direct face: same cause (a theorem header's
/// universe metavariables are not made rigid first —
/// `levelMVarToParamHeaders`), same target. So on the declaration-count axis
/// this face reads as pass → fail; on the "is it Lean's theorem" axis it is
/// wrong-universe → refused. The narrowness is measured and pinned by the
/// controls below: two carriers, or one `Type _` carrier (`imax (u+1) (u+1)`
/// is a `max`), never posed the equation.
#[test]
fn test_level_occurs_eta_expanded_congr_fun_over_one_sort_hole_terminates_fail_closed() {
    assert_funnel_refuses_cycle_before_running_fixture();
    assert_elaborates(
        "",
        "theorem e2 {α β : Sort _} {F G : α → β} (h : F = G) : ∀ x, F x = G x :=\n  \
         fun x => congrFun h x\n\
         theorem e3 {β : Type _} {F G : β → β} (h : F = G) : ∀ x, F x = G x :=\n  \
         fun x => congrFun h x\n",
        "controls: two `Sort _` carriers, one `Type _` carrier",
    );
    for fixture in [
        "theorem e1 {β : Sort _} {F G : β → β} (h : F = G) : ∀ x, F x = G x :=\n  \
         fun x => congrFun h x\n",
        "theorem e4 {β : Sort _} {F G : β → β → β} (h : F = G) : ∀ x y, F x y = G x y :=\n  \
         fun x y => congrFun (congrFun h x) y\n",
    ] {
        let refusal = elab_after("", fixture).expect(
            "OPEN gap CLOSED: the eta-expanded `congrFun` over one `Sort _` binder now \
             elaborates — replace this refusal pin with `assert_elaborates` PLUS a use at \
             `Prop`, so a pass by monomorphization to `Type` cannot satisfy it",
        );
        assert!(
            refusal.contains("unresolved universe level equation after postponement"),
            "the refusal must be the level drain's fail-closed report, got: {refusal}"
        );
    }
}
