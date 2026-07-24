// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Olean env-extension restore, increment 1 — elaborator-level USE proof
//! (#olean-env-ext-restore).
//!
//! `Lean.Meta.instanceExtension` entries decoded from a real toolchain
//! `.olean` must not merely land in the kernel registry: `resolve_instance`
//! must actually synthesize with them. This test resolves a `MonadLift` goal
//! against an imported (not hand-registered) Init.Prelude environment and
//! pins the PROVENANCE of the winning candidate: the registration the
//! elaborator consumed carries Lean's decoded priority 1000, which the
//! pre-decoder import could not produce (its shape heuristic fabricates
//! `DEFAULT_INSTANCE_PRIORITY = 100` for every instance it registers).
//!
//! The audit §5 follow-up landed (lane-B increment 0): the resolver now
//! consumes `InstanceEntry.synthOrder` (decoded from the olean) and the
//! restored transitivity instances (`instMonadLiftTOfMonadLift`, …) DRIVE
//! resolutions — pinned end-to-end in `tests/synth_order_e2e.rs`. See
//! `docs/plans/OLEAN_ENV_EXT_AUDIT_2026-07-09.md` §5 and
//! `designs/2026-07-09-olean-env-ext-restore.md`.

use clean_elab::ElabCtx;
use clean_kernel::env::Environment;
use clean_kernel::expr::{Expr, ExprKind};
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_olean::load_module_with_deps;
use std::path::PathBuf;

/// The pinned toolchain whose `InstanceEntry` layout the decoder targets.
const PINNED_TOOLCHAIN: &str = "leanprover--lean4---v4.30.0-rc2";

/// Lean's default instance priority; Clean's heuristic fabricates 100.
const LEAN_DEFAULT_PRIORITY: u32 = 1000;

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

#[test]
fn test_resolution_over_imported_prelude_uses_decoded_instance_registration() {
    let Some(lib) = v4_30_lib_path() else {
        eprintln!("Skipping test: {PINNED_TOOLCHAIN} not installed");
        return;
    };

    let mut env = Environment::new();
    load_module_with_deps(&mut env, "Init.Prelude", &[lib]).expect("Init.Prelude should import");

    // Goal: `MonadLift Id (ReaderT Nat Id)` (all universes 0). The only
    // candidate is `ReaderT.instMonadLift : MonadLift m (ReaderT ρ m)` — a
    // persisted `@[instance]` decoded from the olean's instanceExtension.
    let zero = Level::zero();
    let id = Expr::const_(Name::interned("Id"), vec![zero.clone()]);
    let reader_t_nat_id = Expr::app(
        Expr::app(
            Expr::const_(Name::interned("ReaderT"), vec![zero.clone(), zero.clone()]),
            Expr::const_(Name::interned("Nat"), Vec::<Level>::new()),
        ),
        id.clone(),
    );
    let goal = Expr::app(
        Expr::app(
            Expr::const_(
                Name::interned("MonadLift"),
                vec![zero.clone(), zero.clone(), zero],
            ),
            id,
        ),
        reader_t_nat_id,
    );

    let mut ctx = ElabCtx::new(&env);
    let witness = ctx
        .resolve_instance(&goal)
        .expect("MonadLift Id (ReaderT Nat Id) should resolve over the imported environment");

    let mut consts = Vec::new();
    collect_consts(&witness, &mut consts);
    let winner = Name::interned("ReaderT.instMonadLift");
    assert!(
        consts.contains(&winner),
        "the synthesized witness must be built from ReaderT.instMonadLift, \
         got constants: {consts:?}"
    );

    // Provenance: the registration the elaborator snapshotted for the winner
    // carries the DECODED priority (Lean default 1000). The pre-decoder
    // import could only ever register it at the fabricated 100, so this pins
    // that the resolution above consumed the restored extension entry.
    let registration = env
        .get_class_instances(&Name::interned("MonadLift"))
        .iter()
        .find(|i| i.name == winner)
        .cloned()
        .expect("ReaderT.instMonadLift should be registered for class MonadLift");
    assert_eq!(
        registration.priority, LEAN_DEFAULT_PRIORITY,
        "the winning candidate's registration must carry the decoded \
         priority (1000), not the heuristic's fabricated 100"
    );

    // The restored transitivity instance is present in the same snapshot
    // (its synthOrder-driven resolutions are pinned in synth_order_e2e.rs).
    assert!(
        env.is_instance(&Name::interned("instMonadLiftTOfMonadLift")),
        "instMonadLiftTOfMonadLift must be registered from the decoded entries"
    );
}
