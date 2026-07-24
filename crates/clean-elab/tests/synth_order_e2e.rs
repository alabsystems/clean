// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Olean env-extension restore, lane-B increment 0 — synthOrder-driven
//! instance resolution (#olean-env-ext-restore).
//!
//! Lean persists, per `@[instance]`, the order in which the instance's
//! binder sub-goals must be synthesized (`InstanceEntry.synthOrder`,
//! `Lean/Meta/Instances.lean:46-60`, computed by `computeSynthOrder`,
//! `Instances.lean:145-229`; consumed by `getSubgoals`,
//! `Lean/Meta/SynthInstance.lean:337`). Clean's decoder now restores the
//! field and `resolve_instance` schedules a candidate's `[inst]` sub-goals
//! in that order, propagating each sub-goal's metavariable solutions to the
//! later ones.
//!
//! This turns the audit §5 reproducer (`crates/clean-elab/examples/
//! probe_resolve.rs`) into pinned tests: transitivity-style instances whose
//! explicit binders are determined only by solving an earlier sub-goal
//! (`instMonadLiftTOfMonadLift : (m n o) → [MonadLift n o] →
//! [MonadLiftT m n] → MonadLiftT m o`, persisted synthOrder `[3, 4]`) can
//! now DRIVE a resolution, where previously they registered but every
//! `MonadLiftT`-chain goal failed.
//!
//! Trust posture: elaboration metadata only. Every synthesized witness here
//! is re-checked by the unmodified kernel (`infer_type` + `is_def_eq`
//! against the goal) and pinned to an empty domain-axiom closure.

use clean_elab::ElabCtx;
use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::TypeChecker;
use clean_olean::load_module_with_deps;
use std::path::PathBuf;

/// The pinned toolchain whose `InstanceEntry` layout the decoder targets.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

/// Locate the pinned v4.30.0-rc2 stdlib, or `None` to skip.
fn v4_30_lib_path() -> Option<PathBuf> {
    let home = std::env::var("HOME").ok()?;
    let lib = PathBuf::from(home)
        .join(".elan/toolchains")
        .join(PINNED_TOOLCHAIN)
        .join("lib/lean");
    lib.exists().then_some(lib)
}

/// Collect every `Const` name mentioned in an expression.
fn collect_consts(expr: &Expr, out: &mut Vec<Name>) {
    match expr.kind() {
        ExprKind::Const(name, _) => out.push(name.clone()),
        ExprKind::App(f, a) => {
            collect_consts(f, out);
            collect_consts(a, out);
        }
        ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
            collect_consts(ty, out);
            collect_consts(body, out);
        }
        ExprKind::Let(_, ty, val, body, _) => {
            collect_consts(ty, out);
            collect_consts(val, out);
            collect_consts(body, out);
        }
        ExprKind::Proj(_, _, inner) | ExprKind::MData(_, inner) => collect_consts(inner, out),
        _ => {}
    }
}

/// Kernel re-check: the witness must type-check and its type must be
/// definitionally equal to the goal. This is the trust gate — resolution is
/// elaboration metadata; the unmodified kernel decides.
fn assert_kernel_checks(env: &Environment, witness: &Expr, goal: &Expr, what: &str) {
    let tc = TypeChecker::new(env);
    let ty = tc
        .infer_type(witness)
        .unwrap_or_else(|e| panic!("{what}: synthesized witness must kernel-infer, got {e:?}"));
    assert!(
        tc.is_def_eq(&ty, goal),
        "{what}: witness type must be def-eq to the goal\n  witness type: {ty:?}\n  goal: {goal:?}"
    );
}

/// Every constant a witness mentions must have an EMPTY domain-axiom
/// closure — instance synthesis over imported Init must bottom out in real
/// definitions, never in axioms or trust markers.
fn assert_empty_axiom_closure(env: &Environment, witness: &Expr, what: &str) {
    let mut consts = Vec::new();
    collect_consts(witness, &mut consts);
    for c in &consts {
        if let Some(deps) = env.axiom_deps(c) {
            assert!(
                deps.is_empty(),
                "{what}: constant {c} in the witness has non-empty axiom closure: {deps:?}"
            );
        }
    }
}

fn mk_monad_lift_t(m: Expr, n: Expr) -> Expr {
    let zero = Level::zero();
    Expr::app(
        Expr::app(
            Expr::const_(
                Name::interned("MonadLiftT"),
                vec![zero.clone(), zero.clone(), zero],
            ),
            m,
        ),
        n,
    )
}

/// `EStateM String Nat` — a Prelude base monad with NO shortcut
/// `MonadLiftT`-conclusion instance, so a lifted-stack goal over it can ONLY
/// resolve through the transitivity instance.
fn mk_estate_m() -> Expr {
    let zero = Level::zero();
    Expr::app(
        Expr::app(
            Expr::const_(Name::interned("EStateM"), vec![zero]),
            Expr::const_(Name::interned("String"), Vec::<Level>::new()),
        ),
        Expr::const_(Name::interned("Nat"), Vec::<Level>::new()),
    )
}

/// `ReaderT Bool base`.
fn mk_reader_t_bool(base: Expr) -> Expr {
    let zero = Level::zero();
    Expr::app(
        Expr::app(
            Expr::const_(Name::interned("ReaderT"), vec![zero.clone(), zero]),
            Expr::const_(Name::interned("Bool"), Vec::<Level>::new()),
        ),
        base,
    )
}

/// POSITIVE, transitivity-only chain:
/// `MonadLiftT (EStateM String Nat) (ReaderT Bool (EStateM String Nat))`.
///
/// Sub-goal scheduling per the DECODED synthOrder `[3, 4]`:
/// binder 3 `[MonadLift ?n (ReaderT Bool (EStateM String Nat))]` resolves
/// via `ReaderT.instMonadLift`, pinning the middle monad
/// `?n := EStateM String Nat`; binder 4 `[MonadLiftT (EStateM String Nat)
/// ?n]` then closes reflexively (`instMonadLiftT`). Before this increment
/// the goal failed outright (audit §5).
#[test]
fn test_transitivity_chain_resolves_via_decoded_synth_order() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // The decoded synthOrder must be registered for the driving instance
    // (Lean persists [3, 4] for instMonadLiftTOfMonadLift; verified against
    // the v4.30.0-rc2 Init.Prelude olean).
    assert_eq!(
        env.get_instance_synth_order(&Name::interned("instMonadLiftTOfMonadLift")),
        Some(&[3usize, 4][..]),
        "instMonadLiftTOfMonadLift must carry the decoded synthOrder [3, 4]"
    );

    let base = mk_estate_m();
    let stacked = mk_reader_t_bool(base.clone());
    let goal = mk_monad_lift_t(base, stacked);

    let mut ctx = ElabCtx::new(&env);
    let witness = ctx
        .resolve_instance(&goal)
        .expect("MonadLiftT (EStateM String Nat) (ReaderT Bool (EStateM String Nat)) must resolve");

    // The witness must be BUILT FROM the transitivity instance and both legs.
    let mut consts = Vec::new();
    collect_consts(&witness, &mut consts);
    let head = witness.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::interned("instMonadLiftTOfMonadLift")),
        "witness head must be instMonadLiftTOfMonadLift, got {head:?}"
    );
    for leg in ["ReaderT.instMonadLift", "instMonadLiftT"] {
        assert!(
            consts.contains(&Name::interned(leg)),
            "witness must contain the {leg} leg, got constants: {consts:?}"
        );
    }

    assert_kernel_checks(&env, &witness, &goal, "EStateM/ReaderT transitivity chain");
    assert_empty_axiom_closure(&env, &witness, "EStateM/ReaderT transitivity chain");
}

/// POSITIVE, the audit §5 reproducer shape: `MonadLiftT Id (ReaderT Nat Id)`
/// over an environment where `Id` genuinely exists (`Init.Control.Id`; the
/// original probe pinned this chain against Init.Prelude alone, where `Id`
/// is not even defined). Any Lean-valid witness is acceptable — Prelude and
/// Init.Control.Id together provide two (`instMonadLiftTOfMonadLift` and
/// `Id.instMonadLiftTOfPure`, both priority 1000; Clean's exact-head tier
/// picks the latter, matching Lean's most-recently-declared-first
/// preference) — but it must kernel-check against the goal with an empty
/// axiom closure.
#[test]
fn test_id_reader_chain_resolves_and_kernel_checks() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Control.Id", &[lib])
        .expect("Init.Control.Id should import");

    let zero = Level::zero();
    let id = Expr::const_(Name::interned("Id"), vec![zero.clone()]);
    let reader_nat_id = Expr::app(
        Expr::app(
            Expr::const_(Name::interned("ReaderT"), vec![zero.clone(), zero]),
            Expr::const_(Name::interned("Nat"), Vec::<Level>::new()),
        ),
        id.clone(),
    );
    let goal = mk_monad_lift_t(id, reader_nat_id);

    let mut ctx = ElabCtx::new(&env);
    let witness = ctx
        .resolve_instance(&goal)
        .expect("MonadLiftT Id (ReaderT Nat Id) must resolve (audit §5 reproducer)");

    assert_kernel_checks(&env, &witness, &goal, "Id/ReaderT chain");
    assert_empty_axiom_closure(&env, &witness, "Id/ReaderT chain");
}

/// NEGATIVE: nothing lifts a ReaderT stack back DOWN into its base monad.
/// The search must fail LOUDLY (return None — the caller then reports an
/// unresolved instance) and in bounded time: the transitivity candidate
/// regenerates `MonadLiftT ?m ?n`-shaped sub-goals, which the resolver's
/// cycle detection (normalized goal already on the active DFS path) and
/// depth cap must cut off. The generous wall-clock bound guards against
/// reintroducing exponential candidate ping-pong, not as a benchmark.
#[test]
fn test_unsatisfiable_downlift_fails_loud_in_bounded_time() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    let base = mk_estate_m();
    let stacked = mk_reader_t_bool(base.clone());
    let goal = mk_monad_lift_t(stacked, base);

    let mut ctx = ElabCtx::new(&env);
    let start = std::time::Instant::now();
    let result = ctx.resolve_instance(&goal);
    let elapsed = start.elapsed();
    assert!(
        result.is_none(),
        "MonadLiftT (ReaderT Bool (EStateM String Nat)) (EStateM String Nat) must NOT resolve"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(10),
        "unsatisfiable chain must fail in bounded time, took {elapsed:?}"
    );
}
