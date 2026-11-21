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
//! Historical mutation check: with the funnel's check disabled the
//! fixture below passed 2.5 GB and was killed; with it, it finishes in
//! seconds.

use crate::tests_pkg4_unifier::{assert_elaborates, elab_after, elab_into};
use crate::unify::MetaState;
use crate::FileContext;
use clean_kernel::name::Name;
use clean_kernel::{Environment, ExprKind, Level, TypeChecker};

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

/// Expected-directed body elaboration permits the direct form without
/// weakening the cycle funnel. Require its single unrestricted universe
/// parameter and real uses at Prop, Bool and a higher type; accidental
/// monomorphization cannot satisfy these controls. The eta forms below retain
/// their separate unresolved-header refusal pins.
#[test]
fn test_level_occurs_congr_fun_over_one_sort_hole_preserves_polymorphism() {
    assert_funnel_refuses_cycle_before_running_fixture();
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let source =
        include_str!("../../../tests/fixtures/congrfun_universe_oracles/declarations.lean");
    // The fixture is the exact source the recorded Lean runs accepted.
    let oracles: serde_json::Value = serde_json::from_str(include_str!(
        "../../../tests/fixtures/congrfun_universe_oracles/declaration-results.json"
    ))
    .expect("oracle results parse");
    let digest = {
        use sha2::Digest;
        let bytes = sha2::Sha256::digest(source.as_bytes());
        bytes.iter().map(|b| format!("{b:02x}")).collect::<String>()
    };
    let runs = oracles.as_array().expect("oracle results are a list");
    assert_eq!(runs.len(), 3, "three pinned Lean profiles");
    for run in runs {
        assert_eq!(
            run["source_sha256"].as_str(),
            Some(digest.as_str()),
            "{run}"
        );
        assert_eq!(run["exit_code"].as_i64(), Some(0), "Lean accepts: {run}");
    }
    if let Some(error) = elab_into(&mut env, &mut context, source) {
        panic!("all three actual Lean profiles accept these universe uses: {error}");
    }
    let q = env
        .get_const(&Name::from_string("q"))
        .expect("q registered");
    assert_eq!(
        q.level_params.len(),
        1,
        "the actual Lean header has one universe"
    );
    let ExprKind::Pi(_, domain, _) = q.type_.kind() else {
        panic!("q must bind its carrier: {}", q.type_);
    };
    let ExprKind::Sort(level) = domain.kind() else {
        panic!("q's carrier must range over Sort u: {domain}");
    };
    assert!(
        matches!(level, Level::Param(name) if q.level_params.contains(name)),
        "q must retain an unrestricted universe, got {level}"
    );
    for name in ["q", "q_at_prop", "q_at_bool", "q_at_higher_type"] {
        let name = Name::from_string(name);
        let info = env
            .get_const(&name)
            .expect("checked declaration registered");
        let proof = info.value.as_ref().expect("proof has a value");
        let tc = TypeChecker::new(&env);
        let inferred = tc.infer_type(proof).expect("proof independently checks");
        assert!(tc.is_def_eq(&inferred, &info.type_));
        assert!(env.axiom_deps(&name).expect("axiom closure").is_empty());
    }
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
/// Before expected-directed bodies, the binder at `Sort ?u` did not pin `?b`; the equations
/// `?u =?= imax ?u ?v` reach the level solver, and the declaration fails
/// closed rather than accepting a monomorphic theorem. These eta forms still
/// retain the separate header-rigidity obligation (a theorem header's
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
