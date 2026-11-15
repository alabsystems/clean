// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The import gate over Lean v4.30.0-rc2's own `Init`: citations the
//! extension-binding worlds (`src/recheck_closed/extension_binding_pins.rs`)
//! let through, and the forgeries under v4.30's names that must still be
//! refused. The worlds' rows themselves are re-derived by
//! `src/recheck_closed/extension_binding_lean_tests.rs`.
//!
//! Until 2026-09-28 the table pinned Lean v4.8.0 only, so every citation whose
//! cone reached `Nat.add`, `Nat.beq`, … of the workspace pin's `Init` was
//! refused by `clean check --imports-prefer-olean` ("by-name kernel reduction
//! … not bound to this declaration"): `Mathlib/Order/Basic.lean` fell from 151
//! credited declarations to 47. Against that table the honest half of each
//! forged arm fails (a v4.30 `Nat.mul` citation is refused on `Nat.add`); the
//! forged halves are refused under both tables. Behind that wall stood a
//! second one the same citations hit next — a v4.30 `BitVec.ofFin` refused
//! because the prelude also evaluates that name natively — which the
//! `…_through_bitvec` arm pins.
//!
//! Every arm replays `Init.Prelude` only: a debug-build replay of every key's
//! cone runs the kernel's certificate path over `String`'s and `autoParam`'s
//! whole closures and did not finish in 30 minutes.
//!
//! Two worlds, because the base changes the fingerprint: over an EMPTY base
//! (`Environment::for_lean_replay`, the re-check lanes) every key is v4.30's
//! own; over the import-mode prelude (`clean check --imports-prefer-olean`) the
//! importer keeps the prelude's declaration of a shared name, so an imported
//! key's cone reaches it (`Nat.add`'s matcher reaches the prelude's
//! `Nat.casesOn`). The measurement and review are in
//! `reports/2026-09-28-extension-binding-v4-30.md`.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use clean_kernel::env::{ConstantInfo, ConstantKind, Environment, Reducibility, TrustedEnvExt};
use clean_kernel::expr::{BinderInfo, Expr};
use clean_kernel::name::Name;
use clean_olean::recheck_closed::{recheck_closed, ClosedRecheckOptions, ClosedRecheckRefusal};
use clean_olean::{load_module_with_deps, ImportedConeGate};

/// The workspace pin whose `Init` these arms replay.
const PINNED: &str = "v4.30.0-rc2";

/// The pinned toolchain's `lib/lean`, through the repository's own locator;
/// it must be `PINNED`'s, so a pin move cannot pass these arms on another
/// release's `Init`.
fn pinned_lib() -> PathBuf {
    let expected = format!("leanprover/lean4:{PINNED}");
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        expected,
        "this battery replays the {PINNED} Init; the workspace pin moved"
    );
    let lib = clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (this battery replays lean-{PINNED})"));
    let toolchain_dir = lib
        .parent()
        .and_then(Path::parent)
        .and_then(Path::file_name)
        .map(|n| n.to_string_lossy().into_owned())
        .unwrap_or_default();
    assert!(
        toolchain_dir.ends_with(&format!("---{PINNED}")),
        "the pinned toolchain is not {PINNED} ({toolchain_dir})"
    );
    lib
}

fn load(mut env: Environment, module: &str) -> Environment {
    let lib = pinned_lib();
    load_module_with_deps(&mut env, module, std::slice::from_ref(&lib))
        .unwrap_or_else(|e| panic!("load {module} ({}): {e}", lib.display()));
    env
}

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn declares(env: &Environment, name: &Name) -> bool {
    env.get_const(name).is_some()
        || env.get_inductive(name).is_some()
        || env.get_constructor(name).is_some()
        || env.get_recursor(name).is_some()
}

fn refused_binding_of<'a>(refusals: &'a [ClosedRecheckRefusal], key: &str) -> Option<&'a str> {
    refusals.iter().find_map(|r| match r {
        ClosedRecheckRefusal::ExtensionBindingMismatch { name, table, .. } if name == key => {
            Some(table.as_str())
        }
        _ => None,
    })
}

/// `Nat.add := fun a b => a`, imported structurally (never type-checked, as
/// an `.olean` payload is) BEFORE v4.30's `Init.Prelude`: the importer keeps
/// the first declaration of a name, so every v4.30 declaration that mentions
/// `Nat.add` is loaded against this one.
fn forge_nat_add(env: &mut Environment) {
    let nat = Expr::const_(n("Nat"), vec![]);
    let ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );
    let value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat, Expr::bvar(1)),
    );
    let rejected = env.extend_constants_structural(std::iter::once(ConstantInfo {
        name: n("Nat.add"),
        level_params: vec![],
        type_: ty,
        value: Some(value),
        is_reducible: false,
        reducibility: Reducibility::Regular(0),
        kind: ConstantKind::Definition,
    }));
    assert!(
        rejected.is_empty(),
        "the structural tier refused the forgery: {rejected:?}"
    );
}

/// The second wall behind the first: over the import prelude, v4.30's
/// `String.ofList` cone reaches `ByteArray`, `UInt8` and `BitVec`, whose
/// constructor `BitVec.ofFin` the prelude's native-reducer table ALSO
/// evaluates. The gate refused that as a `NativeReducerCollision` until
/// 2026-09-28 (every `String`- or `autoParam`-reaching Mathlib citation); it
/// is re-admitted now, because the kernel fires that reducer only over a
/// canonical `BitVec.ofFin` (`clean-kernel/src/env/native_fold_authority.rs`).
#[test]
fn test_import_prelude_gate_credits_a_v4_30_cone_through_bitvec() {
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    assert!(
        base.get_native_reducer(&n("BitVec.ofFin")).is_some() && !declares(&base, &n("BitVec")),
        "the fixture's premise: the prelude evaluates BitVec.ofFin and does not declare BitVec"
    );
    let mut gate = ImportedConeGate::new(&base);
    let env = load(base.clone(), "Init.Prelude");
    // v4.30's `BitVec.ofFin` is a structure constructor, never a fold head the
    // kernel's authority admits, so the prelude's reducer cannot fire on it.
    assert!(env.get_constructor(&n("BitVec.ofFin")).is_some());
    assert!(!env.native_fold_authorized(&n("BitVec.ofFin")));
    let verdict = gate.check(&env, &BTreeSet::from([n("String.ofList")]));
    assert!(verdict.passed(false), "{}", verdict.refusal_summary(false));
    assert!(verdict
        .untrusted_in_cone
        .iter()
        .any(|m| m == "BitVec.ofFin"));
}

/// A forged `Nat.add` under v4.30's names, over an empty base: refused by the
/// binding, by name, and so is everything that depends on it.
/// The same citation over the honest `Init.Prelude` is re-admitted.
#[test]
fn test_forged_nat_add_under_v4_30_names_is_refused_over_an_empty_base() {
    let target = BTreeSet::from([n("Nat.mul")]);
    let honest = load(Environment::for_lean_replay(), "Init.Prelude");
    let run = recheck_closed(&honest, &target, &ClosedRecheckOptions::default());
    assert!(run.report.passed(), "{}", run.report.verdict_sentence());
    assert!(run
        .report
        .extension_keys_bound
        .iter()
        .any(|k| k == "Nat.add"));

    let mut forged = Environment::for_lean_replay();
    forge_nat_add(&mut forged);
    let forged = load(forged, "Init.Prelude");
    let run = recheck_closed(&forged, &target, &ClosedRecheckOptions::default());
    assert!(!run.report.passed(), "{}", run.report.verdict_sentence());
    assert!(
        refused_binding_of(&run.report.refusals, "Nat.add").is_some(),
        "the forged Nat.add must be refused by its binding: {:?}",
        run.report.refusals
    );
    assert!(run.replayed.get_const(&n("Nat.mul")).is_none());
}

/// The same forgery through the production gate, over the import-mode prelude
/// `clean check --imports-prefer-olean` snapshots: the honest citation is
/// credited, the forged one is refused on `Nat.add`'s binding.
#[test]
fn test_forged_nat_add_under_v4_30_names_is_refused_by_the_import_gate() {
    let target = BTreeSet::from([n("Nat.mul")]);
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");

    let mut gate = ImportedConeGate::new(&base);
    let honest = load(base.clone(), "Init.Prelude");
    let verdict = gate.check(&honest, &target);
    assert!(verdict.passed(false), "{}", verdict.refusal_summary(false));

    let mut gate = ImportedConeGate::new(&base);
    let mut forged = base.clone();
    forge_nat_add(&mut forged);
    let forged = load(forged, "Init.Prelude");
    let verdict = gate.check(&forged, &target);
    assert!(!verdict.passed(true));
    assert!(
        refused_binding_of(&verdict.refusals, "Nat.add").is_some(),
        "the forged Nat.add must be refused by its binding: {:?}",
        verdict.refusals
    );
}

/// A forgery ONE LEVEL BELOW a key, under v4.30's own names, through the
/// production gate over the import-mode prelude: `Nat.add._f` (the functional
/// v4.30's structural `Nat.add` is `Nat.brecOn` of) replaced by the
/// well-typed `fun x f x_1 => x_1`, so `Nat.add a b` δ-reduces to `a`, while
/// `Nat.add` itself is v4.30's own bytes. The key's fingerprint hashes its
/// whole cone, so it matches NO world's row — the union of three worlds admits
/// exactly the reviewed cones, never a cone that shares only the key's own
/// declaration with one of them — and the refusal names every world's row it
/// was compared against.
#[test]
fn test_forged_nat_add_functional_under_v4_30_names_is_refused_by_the_import_gate() {
    use clean_kernel::expr::ExprKind;
    let target = BTreeSet::from([n("Nat.mul")]);
    let base = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    let functional = n("Nat.add._f");

    // The honest `Nat.add._f`, for its type: `(x : Nat) → Nat.below x → Nat → Nat`.
    let honest = load(base.clone(), "Init.Prelude");
    let honest_f = honest
        .get_const(&functional)
        .expect("v4.30 Init.Prelude declares Nat.add._f")
        .clone();
    let ExprKind::Pi(_, x_ty, rest) = honest_f.type_.kind() else {
        panic!("Nat.add._f's type is not a Pi: {:?}", honest_f.type_)
    };
    let ExprKind::Pi(_, below_ty, _) = rest.kind() else {
        panic!(
            "Nat.add._f's type has no second binder: {:?}",
            honest_f.type_
        )
    };
    let nat = Expr::const_(n("Nat"), vec![]);
    let forged_value = Expr::lam(
        BinderInfo::Default,
        (**x_ty).clone(),
        Expr::lam(
            BinderInfo::Default,
            (**below_ty).clone(),
            Expr::lam(BinderInfo::Default, nat, Expr::bvar(0)),
        ),
    );

    let mut forged = base.clone();
    let rejected = forged.extend_constants_structural(std::iter::once(ConstantInfo {
        value: Some(forged_value),
        ..honest_f
    }));
    assert!(
        rejected.is_empty(),
        "the structural tier refused the forgery: {rejected:?}"
    );
    let forged = load(forged, "Init.Prelude");
    let nat_add = forged
        .get_const(&n("Nat.add"))
        .expect("v4.30 Nat.add is loaded over the forgery");
    assert_eq!(
        nat_add.value,
        honest
            .get_const(&n("Nat.add"))
            .and_then(|c| c.value.clone()),
        "the key's own declaration is v4.30's, byte for byte"
    );

    let mut gate = ImportedConeGate::new(&base);
    let verdict = gate.check(&forged, &target);
    assert!(!verdict.passed(true));
    let refusal = verdict
        .refusals
        .iter()
        .find_map(|r| match r {
            ClosedRecheckRefusal::ExtensionBindingMismatch { name, expected, .. }
                if name == "Nat.add" =>
            {
                Some(expected.clone())
            }
            _ => None,
        })
        .unwrap_or_else(|| {
            panic!(
                "the forged functional must be refused on Nat.add's binding: {:?}",
                verdict.refusals
            )
        });
    let expected = refusal.expect("the pinned table has rows for Nat.add");
    for world in [
        "lean-v4.8.0-core",
        "lean-v4.30.0-rc2-core",
        "clean-import+lean-v4.30.0-rc2-core",
    ] {
        assert!(
            expected.contains(world),
            "the refusal must name {world}'s row: {expected}"
        );
    }
}
