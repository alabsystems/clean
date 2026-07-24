// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Olean env-extension restore, lane-B increment 2 — elaborator-level USE
//! proof for decoded `Lean.classExtension` out-params (#olean-env-ext-restore).
//!
//! `ClassEntry.outParams` decoded from a real toolchain `.olean` must not
//! merely land in the kernel registry: they must reach the elaborator's
//! `InstanceTable` — the exact structure `resolve_instance` reads for two-phase
//! out-param unification (`crates/clean-elab/src/infer/instance.rs:244-390`,
//! `ClassInfo::out_params`). This test snapshots that table over an imported
//! (not hand-registered) Init.Prelude and pins the restored positions, then
//! drives a resolution over the restored out-param class to show the two-phase
//! path executes green with the real metadata.
//!
//! Consumption scope (documented gap): a resolution whose OUTCOME diverges —
//! succeeding only because a position is treated as an out-param — needs an
//! out-param class with competing instances whose non-out arguments coincide,
//! i.e. heavier import machinery than a single `.olean`. That is deferred; the
//! InstanceTable snapshot below is the sanctioned proof that the decoded
//! `outParams` reach the consumer. See
//! `docs/plans/OLEAN_ENV_EXT_AUDIT_2026-07-09.md` §5 and
//! `designs/2026-07-09-olean-env-ext-restore.md`.

use clean_elab::ElabCtx;
use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;
use std::path::PathBuf;

/// The pinned toolchain whose `ClassEntry` layout the decoder targets.
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
        ExprKind::MData(_, inner) | ExprKind::Proj(_, _, inner) => collect_consts(inner, out),
        _ => {}
    }
}

#[test]
fn test_decoded_out_params_reach_the_instance_table() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // `ElabCtx::new` snapshots `env.classes()` into the InstanceTable that
    // `resolve_instance` consumes; the decoded out-params must survive that
    // snapshot verbatim.
    let ctx = ElabCtx::new(&env);
    let table = ctx.instances();

    let membership = table
        .get_class(&Name::interned("Membership"))
        .expect("Membership must reach the InstanceTable as a class (it exists only via classExtension — no imported instance)");
    assert_eq!(
        membership.out_params,
        vec![0],
        "Membership's decoded outParam [0] must reach the resolver's ClassInfo"
    );

    let hadd = table
        .get_class(&Name::interned("HAdd"))
        .expect("HAdd must reach the InstanceTable as a class");
    assert_eq!(
        hadd.out_params,
        vec![2],
        "HAdd's decoded outParam [2] must reach the resolver's ClassInfo (was [] pre-increment)"
    );
}

#[test]
fn test_resolution_over_restored_out_param_class_runs() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };
    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // `HAdd` now carries out_params [2]; resolving a concrete `HAdd Nat Nat Nat`
    // goal exercises the two-phase out-param unification (phase 1 unifies the
    // α/β inputs, phase 2 the γ out-position) against the restored class and
    // must synthesize `instHAdd`.
    let zero = Level::zero();
    let nat = Expr::const_(Name::interned("Nat"), Vec::<Level>::new());
    let goal = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::interned("HAdd"),
                    vec![zero.clone(), zero.clone(), zero],
                ),
                nat.clone(),
            ),
            nat.clone(),
        ),
        nat,
    );

    let mut ctx = ElabCtx::new(&env);
    let witness = ctx
        .resolve_instance(&goal)
        .expect("HAdd Nat Nat Nat must resolve over imported Init.Prelude");

    let head = witness.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if *n == Name::interned("instHAdd")),
        "witness head must be instHAdd, got {head:?}"
    );
    // The instHAdd witness delegates to the `Add Nat` instance — a sanity check
    // that the two-phase resolution actually threaded the sub-goal.
    let mut consts = Vec::new();
    collect_consts(&witness, &mut consts);
    assert!(
        consts.contains(&Name::interned("instAddNat")),
        "witness must contain the instAddNat leg, got: {consts:?}"
    );
}
