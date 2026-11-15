// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! THE DEFAULT PRELUDE MUST NOT PROVE `False`.
//!
//! Before 2026-09-28 the default `clean check` environment registered
//! `Pure.pure`, `Bind.bind`, `MonadExcept.throw`, the `StateT` operations and
//! the `OptionT` pair as value-less, INSTANCE-LESS axioms. Each type
//! quantifies over an arbitrary type former `m` and returns an inhabitant of
//! `m _`, which no model satisfies: at `m := fun _ => Empty` (or, for
//! `Bind.bind`, the contravariant `m := fun X => X → Empty`) every one of them
//! produces an `Empty`, and `Empty.elim` turns that into `False`.
//!
//! Every term below is one such derivation, spelled against the OLD
//! signatures. With the Lean-faithful class hierarchy
//! (`data_monad_classes.rs`) none of them type-checks any more: `Pure.pure`
//! and `Bind.bind` are projections that need a `Pure m` / `Bind m` instance,
//! which nothing supplies for an empty family; the `StateT` operations and
//! `OptionT.fail` take `[Monad m]`; `MonadExcept.throw` is a projection of a
//! class; `OptionT` is `m (Option α)` by definition. Each test asserts the
//! derivation is REFUSED and — the anti-vacuity half — that a CONTROL with the
//! same head, built the Lean way over a genuine instance, is ACCEPTED, so a
//! refusal cannot come from a missing constant or a mistyped fixture.
//!
//! RED/GREEN record: `docs/issues/2026-09-28-prelude-pure-proves-false.md`.

use super::types::Declaration;
use super::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;

/// The environment a bare `clean check <file>` loads (mirrors
/// `tests_prelude_axiom_ratchet::check_default_env`).
fn check_default_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_monad_list_insts()
        .expect("invariant: init_monad_list_insts is idempotent on with_prelude()");
    env.init_io_ops()
        .expect("invariant: init_io_ops is idempotent on with_prelude()");
    env.init_ulift()
        .expect("invariant: init_ulift is idempotent on with_prelude()");
    env
}

fn c(name: &str, levels: Vec<Level>) -> Expr {
    Expr::const_(Name::from_string(name), levels)
}

fn l0() -> Level {
    Level::zero()
}

fn type0() -> Expr {
    Expr::sort(Level::succ(Level::zero()))
}

fn empty() -> Expr {
    c("Empty", vec![])
}

fn unit() -> Expr {
    c("Unit", vec![])
}

fn unit_unit() -> Expr {
    c("Unit.unit", vec![])
}

fn nat() -> Expr {
    c("Nat", vec![])
}

fn nat_zero() -> Expr {
    c("Nat.zero", vec![])
}

/// `fun (_ : Type) => Empty` — the empty type family.
fn empty_family() -> Expr {
    Expr::lam(BinderInfo::Default, type0(), empty())
}

/// `Empty.elim.{0} False e` — `False` from an inhabitant of `Empty`.
fn false_of_empty(e: Expr) -> Expr {
    Expr::apps(c("Empty.elim", vec![l0()]), [c("False", vec![]), e])
}

/// Try to add `theorem <name> : False := <value>`; `Ok(axiom_deps)` if the
/// kernel accepted it.
fn try_prove_false(env: &mut Environment, name: &str, value: Expr) -> Result<Vec<String>, String> {
    let n = Name::from_string(name);
    env.add_decl(Declaration::Theorem {
        name: n.clone(),
        level_params: vec![],
        type_: c("False", vec![]),
        value,
    })
    .map_err(|e| format!("{e:?}"))?;
    let mut deps: Vec<String> = env
        .axiom_deps(&n)
        .map(|d| d.iter().map(ToString::to_string).collect())
        .unwrap_or_default();
    deps.sort();
    Ok(deps)
}

fn assert_refused(name: &str, value: Expr) {
    let mut env = check_default_env();
    if let Ok(deps) = try_prove_false(&mut env, name, value) {
        panic!(
            "THE DEFAULT PRELUDE PROVES FALSE: `theorem {name} : False` was ACCEPTED by the \
             kernel over Environment::with_prelude() with axiom_deps = {deps:?}"
        );
    }
}

/// `theorem e4d_pure_empty_false : False :=
///    Empty.elim (Pure.pure.{0,0} (fun _ : Type => Empty) Nat Nat.zero)`
/// — the E4d lane's reproduction, spelled against the old 3-argument axiom.
#[test]
fn prelude_pure_pure_at_the_empty_family_does_not_prove_false() {
    let pure_empty = Expr::apps(
        c("Pure.pure", vec![l0(), l0()]),
        [empty_family(), nat(), nat_zero()],
    );
    assert_refused("PreludeFalseProbe.pure", false_of_empty(pure_empty));
}

/// `Bind.bind` at the CONTRAVARIANT family `m X := X → Empty`, `α := Empty`,
/// `β := Unit`: `bind id (fun e => Empty.elim e) : Unit → Empty`, applied to
/// `()`. The empty family alone does not refute `bind` (it takes an `m α`);
/// this one does.
#[test]
fn prelude_bind_bind_at_a_contravariant_family_does_not_prove_false() {
    let m = Expr::lam(
        BinderInfo::Default,
        type0(),
        Expr::arrow(Expr::bvar(0), empty()),
    );
    let id_empty = Expr::lam(BinderInfo::Default, empty(), Expr::bvar(0));
    let unit_to_empty = Expr::arrow(unit(), empty());
    let k = Expr::lam(
        BinderInfo::Default,
        empty(),
        Expr::apps(
            c("Empty.elim", vec![Level::succ(l0())]),
            [unit_to_empty, Expr::bvar(0)],
        ),
    );
    let bound = Expr::apps(
        c("Bind.bind", vec![l0(), l0()]),
        [m, empty(), unit(), id_empty, k],
    );
    assert_refused(
        "PreludeFalseProbe.bind",
        false_of_empty(Expr::app(bound, unit_unit())),
    );
}

/// `MonadExcept.throw.{0,0,0} (ε := Unit) (m := fun _ => Empty) (α := Nat) ()`.
#[test]
fn prelude_monad_except_throw_at_the_empty_family_does_not_prove_false() {
    let thrown = Expr::apps(
        c("MonadExcept.throw", vec![l0(), l0(), l0()]),
        [unit(), empty_family(), nat(), unit_unit()],
    );
    assert_refused("PreludeFalseProbe.throw", false_of_empty(thrown));
}

/// `StateT σ m α` unfolds to `σ → m (α × σ)`, so an instance-less
/// `StateT.pure` / `get` / `set` / `modify` / `modifyGet` over the empty
/// family, applied to a state, is an `Empty`.
#[test]
fn prelude_state_t_operations_at_the_empty_family_do_not_prove_false() {
    let pure = Expr::apps(
        c("StateT.pure", vec![l0(), l0()]),
        [unit(), empty_family(), nat(), nat_zero(), unit_unit()],
    );
    assert_refused("PreludeFalseProbe.stateTPure", false_of_empty(pure));

    let get = Expr::apps(
        c("StateT.get", vec![l0(), l0()]),
        [unit(), empty_family(), unit_unit()],
    );
    assert_refused("PreludeFalseProbe.stateTGet", false_of_empty(get));

    let set = Expr::apps(
        c("StateT.set", vec![l0(), l0()]),
        [unit(), empty_family(), unit_unit(), unit_unit()],
    );
    assert_refused("PreludeFalseProbe.stateTSet", false_of_empty(set));

    let id_unit = Expr::lam(BinderInfo::Default, unit(), Expr::bvar(0));
    let modify = Expr::apps(
        c("StateT.modify", vec![l0(), l0()]),
        [unit(), empty_family(), id_unit, unit_unit()],
    );
    assert_refused("PreludeFalseProbe.stateTModify", false_of_empty(modify));

    let pair = Expr::lam(
        BinderInfo::Default,
        unit(),
        Expr::apps(
            c("Prod.mk", vec![l0(), l0()]),
            [unit(), unit(), Expr::bvar(0), Expr::bvar(0)],
        ),
    );
    let modify_get = Expr::apps(
        c("StateT.modifyGet", vec![l0(), l0()]),
        [unit(), empty_family(), unit(), pair, unit_unit()],
    );
    assert_refused(
        "PreludeFalseProbe.stateTModifyGet",
        false_of_empty(modify_get),
    );
}

/// `OptionT.run (OptionT.fail)` over the empty family: each axiom is
/// satisfiable ALONE, the pair is not — the joint-consistency case a
/// per-axiom reading misses.
#[test]
fn prelude_option_t_run_of_fail_at_the_empty_family_does_not_prove_false() {
    let fail = Expr::apps(c("OptionT.fail", vec![l0(), l0()]), [empty_family(), nat()]);
    let run = Expr::apps(
        c("OptionT.run", vec![l0(), l0()]),
        [empty_family(), nat(), fail],
    );
    assert_refused("PreludeFalseProbe.optionTRunFail", false_of_empty(run));
}

/// CONTROL for every refusal above: the same heads, applied the Lean way over
/// a GENUINE instance, type-check and COMPUTE — so the refusals come from the
/// missing instance, not from a missing constant or a mistyped fixture.
///
/// `@Pure.pure Option (toPure (toApplicative instMonadOption)) Nat 0 ≡ some 0`
/// and `@StateT.get Unit Id Id.instMonad () ≡ ((), ())`, by ordinary δ/ι/β —
/// no by-name reduction is involved (the kernel's monad hook is gone).
#[test]
fn prelude_monad_heads_compute_over_genuine_instances() {
    use crate::env::monad_term::MonadInst;
    use crate::tc::TypeChecker;

    let env = check_default_env();
    let tc = TypeChecker::new(&env);
    let option = c("Option", vec![l0()]);
    let mi = MonadInst {
        u: l0(),
        v: l0(),
        m: option.clone(),
        inst: c("instMonadOption", vec![l0()]),
    };
    let pure0 = mi.pure(nat(), nat_zero());
    let ty = tc
        .infer_type(&pure0)
        .unwrap_or_else(|e| panic!("control: pure over instMonadOption must type-check: {e:?}"));
    assert!(tc.is_def_eq(&ty, &Expr::app(option, nat())));
    let some0 = Expr::apps(c("Option.some", vec![l0()]), [nat(), nat_zero()]);
    assert!(
        tc.is_def_eq(&pure0, &some0),
        "control: pure 0 over Option must reduce to some 0"
    );
    let none = Expr::app(c("Option.none", vec![l0()]), nat());
    assert!(
        !tc.is_def_eq(&pure0, &none),
        "control: pure 0 must NOT be def-eq to none"
    );

    let id = c("Id", vec![l0()]);
    let get = Expr::apps(
        c("StateT.get", vec![l0(), l0()]),
        [unit(), id, c("Id.instMonad", vec![l0()]), unit_unit()],
    );
    let _ = tc
        .infer_type(&get)
        .unwrap_or_else(|e| panic!("control: StateT.get over Id must type-check: {e:?}"));
    let pair = Expr::apps(
        c("Prod.mk", vec![l0(), l0()]),
        [unit(), unit(), unit_unit(), unit_unit()],
    );
    assert!(
        tc.is_def_eq(&get, &pair),
        "control: StateT.get over Id applied to () must reduce to ((), ())"
    );
}
