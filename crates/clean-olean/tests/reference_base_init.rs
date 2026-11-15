// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR1 slice 1: a `ReferenceKernel` whose base is the pinned Lean
//! v4.30.0-rc2 `Init`, every declaration re-checked through the entry
//! (`clean_olean::reference_base_closed`).
//!
//! * The Nat / Bool / Eq core of `Init.Prelude` (with the quotient
//!   primitives a `Quot.lift` citation reaches) is accepted, every constant
//!   in the entry was admitted through it, and the entry then decides
//!   `2 + 2 = 4` by `rfl` and refuses `2 + 2 = 5`.
//! * Negative control: the same cone with ONE declaration tampered (the
//!   type of `Nat.not_succ_le_zero` replaced by `False`) is refused at that
//!   declaration, and its dependent is refused in turn.
//! * Tripwires through the base: Init's `sorryAx`, `Lean.ofReduceBool`,
//!   `Lean.ofReduceNat` and `Lean.trustCompiler` are each refused by the
//!   entry by name, and a constant whose value cites `sorryAx` is refused
//!   with it. Control: the untampered core above admits every unit.
//!
//! These read only the pinned toolchain's library and assert the toolchain
//! directory first, so they never pass silently against the vendor v4.8
//! `.olean`s.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use clean_kernel::env::{ConstantInfo, ConstantKind, Declaration, Environment, TrustedEnvExt};
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{ReferenceRefusal, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{load_module_with_deps, reference_base_closed, ClosedRecheckRefusal};

const PINNED: &str = "v4.30.0-rc2";

fn pinned_lib() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this test reads the {PINNED} Init; the workspace pin moved"
    );
    let lib = clean_olean::require_pinned_lean_lib_path()
        .unwrap_or_else(|e| panic!("{e} (this test reads lean-{PINNED}; KR0 plan step 0.1)"));
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

fn load(module: &str) -> Environment {
    let lib = pinned_lib();
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(&mut env, module, std::slice::from_ref(&lib))
        .unwrap_or_else(|e| panic!("load {module} ({}): {e}", lib.display()));
    env
}

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn names(xs: &[&str]) -> BTreeSet<Name> {
    xs.iter().copied().map(n).collect()
}

/// The Nat / Bool / Eq core this slice admits, plus a quotient citation.
const CORE: [&str; 13] = [
    "Nat.add",
    "Nat.mul",
    "Nat.beq",
    "Nat.eq_of_beq_eq_true",
    "Nat.not_succ_le_zero",
    "Nat.not_lt_zero",
    "Nat.zero_le",
    "Bool",
    "eq_true_of_ne_false",
    "Eq.trans",
    "congrArg",
    "decide_eq_true",
    "Quot.lift",
];

/// `@Eq.{1} Nat (Nat.add a b) c := @Eq.refl.{1} Nat c`.
fn nat_add_rfl(name: &str, a: u64, b: u64, c: u64) -> Declaration {
    let one = || vec![Level::succ(Level::zero())];
    let nat = || Expr::const_(n("Nat"), vec![]);
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(n("Eq"), one()),
            [
                nat(),
                Expr::apps(
                    Expr::const_(n("Nat.add"), vec![]),
                    [Expr::nat_lit(a), Expr::nat_lit(b)],
                ),
                Expr::nat_lit(c),
            ],
        ),
        value: Expr::apps(Expr::const_(n("Eq.refl"), one()), [nat(), Expr::nat_lit(c)]),
    }
}

#[test]
fn test_init_core_is_admitted_through_the_entry_and_a_tampered_declaration_is_refused() {
    let env = load("Init.Prelude");
    let options = ClosedRecheckOptions::default();

    // ── Positive: the core, every member through the entry. ──
    let built = reference_base_closed(&env, &names(&CORE), &options).expect("empty start");
    assert!(
        built.report.passed(),
        "{}\nentry refusals: {:?}",
        built.report.verdict_sentence(),
        built.entry_refusals
    );
    assert!(built.entry_refusals.is_empty());
    assert!(built.report.quotient_primitives_installed);
    assert!(
        built.report.families_replayed >= 5,
        "Nat, Bool, Eq, Decidable, … are families: {:?}",
        built.report
    );
    let admitted = built.admitted.clone();
    for target in CORE {
        // The quotient primitives are installed by the entry's `add_quot`,
        // not admitted from the cone: the cone's copy is compared instead.
        let is_quot = clean_kernel::quot::is_quot_name(&n(target));
        let present = if is_quot {
            built.kernel().environment().get_quot(&n(target)).is_some()
        } else {
            admitted.contains(&n(target))
        };
        assert!(present, "{target} was not admitted");
    }
    let mut k = built.into_kernel().expect("a passing, pinned replay");
    assert_eq!(k.theory_id(), TheoryId::LeanReferenceV1);
    let kenv = k.environment();
    // Nothing served lazily, and nothing in the entry it did not admit.
    assert!(kenv.lazy_source_names().is_empty());
    let mut present: Vec<Name> = kenv.constants().map(|c| c.name.clone()).collect();
    present.sort();
    for name in &present {
        assert!(
            admitted.contains(name) || clean_kernel::quot::is_quot_name(name),
            "{name} is in the entry but was not admitted through it"
        );
        assert_eq!(
            kenv.declaration_verification(name),
            Some(clean_kernel::env::DeclarationVerification::FullKernelCheck),
            "{name}"
        );
    }
    assert!(
        present.len() >= 50,
        "the core cone is not trivially small: {} constants",
        present.len()
    );

    // The entry over this base decides by Lean's Nat extension.
    let before = k.env_digest();
    let token = k
        .add_checked(nat_add_rfl("kr1_two_add_two", 2, 2, 4))
        .expect("2 + 2 = 4 by rfl over pinned Init");
    assert_eq!(token.theory_id(), TheoryId::LeanReferenceV1);
    assert_ne!(k.env_digest(), before);
    let err = k
        .add_checked(nat_add_rfl("kr1_two_add_two_bad", 2, 2, 5))
        .expect_err("2 + 2 = 5 is refused");
    assert!(matches!(err, ReferenceRefusal::Kernel(_)), "got {err:?}");

    // ── Negative control: one tampered declaration. ──
    let mut tampered = env.clone();
    let mut info: ConstantInfo = tampered
        .get_const(&n("Nat.not_succ_le_zero"))
        .expect("Nat.not_succ_le_zero is in Init.Prelude")
        .clone();
    assert_eq!(info.kind, ConstantKind::Theorem);
    info.type_ = Expr::const_(n("False"), vec![]);
    let rejected = tampered.extend_constants_structural(std::iter::once(info));
    assert!(rejected.is_empty(), "{rejected:?}");
    let run = reference_base_closed(&tampered, &names(&CORE), &options).expect("empty start");
    assert!(!run.report.passed());
    assert!(
        run.report.refusals.iter().any(|r| matches!(r,
            ClosedRecheckRefusal::DeclarationRefused { name, error }
                if name == "Nat.not_succ_le_zero" && error.starts_with("reference entry:"))),
        "{:#?}",
        run.report.refusals
    );
    assert!(
        run.entry_refusals
            .iter()
            .any(|(unit, r)| unit == "Nat.not_succ_le_zero"
                && matches!(r, ReferenceRefusal::Kernel(_))),
        "{:?}",
        run.entry_refusals
    );
    // `Nat.not_lt_zero` is proved from it, so it is refused in turn.
    assert!(
        run.report.refusals.iter().any(|r| matches!(r,
            ClosedRecheckRefusal::DependencyRefused { name, .. } if name == "Nat.not_lt_zero")),
        "{:#?}",
        run.report.refusals
    );
    assert!(!run.admitted.contains(&n("Nat.not_succ_le_zero")));
    assert!(run
        .kernel()
        .environment()
        .get_const(&n("Nat.not_succ_le_zero"))
        .is_none());
    assert!(
        run.into_kernel().is_err(),
        "a refusing replay hands out no entry"
    );
}

#[test]
fn test_init_tripwires_are_refused_through_the_entry() {
    let mut env = load("Init.Core");
    // A constant whose value cites `sorryAx`, imported the way `.olean`
    // constants are.
    let nat = Expr::const_(n("Nat"), vec![]);
    let uses_sorry = ConstantInfo::new(
        n("kr1_uses_sorry"),
        vec![],
        nat.clone(),
        Some(Expr::apps(
            Expr::const_(n("sorryAx"), vec![Level::succ(Level::zero())]),
            [nat, Expr::const_(n("Bool.false"), vec![])],
        )),
        false,
    );
    assert_eq!(uses_sorry.kind, ConstantKind::Definition);
    let rejected = env.extend_constants_structural(std::iter::once(uses_sorry));
    assert!(rejected.is_empty(), "{rejected:?}");

    let options = ClosedRecheckOptions::default();
    for tripwire in [
        "sorryAx",
        "Lean.ofReduceBool",
        "Lean.ofReduceNat",
        "Lean.trustCompiler",
    ] {
        assert!(
            env.get_const(&n(tripwire)).is_some(),
            "{tripwire} is declared in pinned Init"
        );
        let run = reference_base_closed(&env, &names(&[tripwire]), &options).expect("empty start");
        // Refused by the entry as a tripwire: itself, or — for the
        // `native_decide` bridges, whose `Lean.reduceBool` / `reduceNat` cite
        // `Lean.trustCompiler` — the tripwire its cone reaches first, with
        // the target refused by the cascade.
        assert!(
            run.entry_refusals
                .iter()
                .all(|(_, r)| matches!(r, ReferenceRefusal::Tripwire { .. }))
                && !run.entry_refusals.is_empty(),
            "{tripwire}: {:?}",
            run.entry_refusals
        );
        assert!(
            run.report.refusals.iter().any(|r| match r {
                ClosedRecheckRefusal::DeclarationRefused { name, .. }
                | ClosedRecheckRefusal::DependencyRefused { name, .. } => name == tripwire,
                _ => false,
            }),
            "{tripwire}: {:#?}",
            run.report.refusals
        );
        assert!(!run.admitted.contains(&n(tripwire)));
        assert!(run.into_kernel().is_err());
    }
    let run =
        reference_base_closed(&env, &names(&["kr1_uses_sorry"]), &options).expect("empty start");
    assert!(
        run.report.refusals.iter().any(|r| matches!(r,
            ClosedRecheckRefusal::DependencyRefused { name, .. } if name == "kr1_uses_sorry")),
        "{:#?}",
        run.report.refusals
    );
    assert!(!run.admitted.contains(&n("kr1_uses_sorry")));

    // Control: the axioms Lean's kernel trusts pass through the same entry.
    let run = reference_base_closed(
        &env,
        &names(&["propext", "Classical.choice", "Quot.sound"]),
        &options,
    )
    .expect("empty start");
    assert!(
        run.report.passed(),
        "{}\n{:?}",
        run.report.verdict_sentence(),
        run.entry_refusals
    );
}
