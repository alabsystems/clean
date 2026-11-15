// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR0 test 2: `String.drop "abc" 1 = String.drop "xbc" 1 := rfl` over the
//! pinned Lean 4.30 `Init` is refused through the reference entry.
//!
//! Lean 4.30's `String.drop` returns a `String.Slice` that remembers the
//! string it was cut from (`Init/Data/String/TakeDrop.lean`), so the two
//! sides differ and Lean's kernel refuses the equation; Clean's reducer
//! returns a `String` literal, under which it is true. On Lean 4.8's `Init`
//! the equation is TRUE (`drop` returned a `String` there), so this test must
//! never run against the vendor v4.8 `.olean`s: it loads only the pinned
//! toolchain's library and asserts both the toolchain directory and the v4.30
//! shape of `String.drop` before it asserts anything else.
//!
//! The entry's base is the dependency-closed replay of `String.drop`'s cone
//! (`clean_olean::recheck_closed`): every constant in it entered through
//! `add_decl` / `add_inductive_core` / `add_quot`, which is what the entry's
//! base walk requires. The imported environment itself is a structural import
//! and is refused by `ReferenceKernel::new` — asserted here too.
//!
//! One test function on purpose: its `Extended` control opens the native-fold
//! authority bypass, which is process-global.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use clean_kernel::env::{native_fold_mint_bypass, Declaration, Environment, KernelTheory};
use clean_kernel::expr::Expr;
use clean_kernel::level::Level;
use clean_kernel::name::Name;
use clean_kernel::{ReferenceKernel, ReferenceRefusal};
use clean_olean::load_module_with_deps;
use clean_olean::recheck_closed::{recheck_closed, ClosedRecheckOptions};

const PINNED: &str = "v4.30.0-rc2";

fn pinned_lib() -> PathBuf {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this test reads the {PINNED} Init; the workspace pin moved"
    );
    let lib = clean_olean::require_pinned_lean_lib_path().unwrap_or_else(|e| {
        panic!("{e} (this test reads lean-{PINNED}; see the KR0 plan step 0.1)")
    });
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

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn drop_(s: &str, k: u64) -> Expr {
    Expr::apps(c("String.drop"), [Expr::str_lit(s), Expr::nat_lit(k)])
}

/// `@Eq.{1} String.Slice lhs rhs := @Eq.refl.{1} String.Slice lhs`.
fn rfl_theorem(name: &str, lhs: Expr, rhs: Expr) -> Declaration {
    let one = || vec![Level::succ(Level::zero())];
    Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(n("Eq"), one()),
            [c("String.Slice"), lhs.clone(), rhs],
        ),
        value: Expr::apps(Expr::const_(n("Eq.refl"), one()), [c("String.Slice"), lhs]),
    }
}

#[test]
fn test_string_drop_disagreement_is_refused_through_the_entry() {
    let lib = pinned_lib();
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(
        &mut env,
        "Init.Data.String.TakeDrop",
        std::slice::from_ref(&lib),
    )
    .unwrap_or_else(|e| panic!("load Init.Data.String.TakeDrop ({}): {e}", lib.display()));

    // The loaded Init is v4.30's: `String.drop : String → Nat → String.Slice`.
    let drop_ty = env
        .get_const(&n("String.drop"))
        .expect("String.drop is loaded")
        .type_
        .clone();
    let mut cited = std::collections::HashSet::new();
    drop_ty.used_constants_dag(clean_kernel::expr::UsedConstants::ConstantsOnly, &mut cited);
    assert!(
        cited.contains(&n("String.Slice")),
        "String.drop does not return a String.Slice: this is not the v4.30 Init ({drop_ty:?})"
    );

    let forged = rfl_theorem("kr0_string_drop_forged", drop_("abc", 1), drop_("xbc", 1));

    // The imported environment is a structural import: not a base.
    assert!(
        matches!(
            ReferenceKernel::new(env.clone()),
            Err(ReferenceRefusal::StructuralProvenance { .. })
        ),
        "an unreplayed .olean import must not pass the base walk"
    );

    // The replayed cone is.
    let run = recheck_closed(
        &env,
        &BTreeSet::from([n("String.drop"), n("Eq"), n("Eq.refl")]),
        &ClosedRecheckOptions::default(),
    );
    assert!(run.report.passed(), "{}", run.report.verdict_sentence());
    // The replay starts from `Environment::default()`, whose native-reducer
    // table is EMPTY (`recheck_closed`), so over it nothing could fold
    // `String.drop` in any theory and the entry's refusal would show nothing
    // about its theory. Register Clean's reducers in the base: then the
    // reducer is present, and what keeps it from firing in the entry is
    // authority (closed for `String.drop` in every theory) and, with
    // authority opened below, the reference theory alone. Unit F2 measured
    // the gap: with the theory rule removed the test stayed green.
    let mut base = run.replayed;
    base.ensure_native_reducers();
    let mut k = ReferenceKernel::new(base).expect("the replayed cone passes the base walk");

    let err = k
        .add_checked(forged.clone())
        .expect_err("Lean's kernel refuses String.drop \"abc\" 1 = String.drop \"xbc\" 1");
    assert!(
        matches!(
            err,
            ReferenceRefusal::Kernel(_) | ReferenceRefusal::TheoryExclusion(_)
        ),
        "got {err:?}"
    );

    // Positive control over the same base: reflexivity is accepted.
    k.add_checked(rfl_theorem(
        "kr0_string_drop_refl",
        drop_("abc", 1),
        drop_("abc", 1),
    ))
    .expect("String.drop \"abc\" 1 = String.drop \"abc\" 1 by rfl");

    // Extended control (extra; the plan does not ask for it). With the fold
    // authority gate open, Clean's `String` reducer fires and the extended
    // theory accepts the disagreement — the term is exactly one an extra-Lean
    // reducer decides.
    env.set_kernel_theory(KernelTheory::Extended);
    // With the gate open, only the entry's theory stands between the reducer
    // and the equation: the entry still refuses it, so the refusal above is
    // the fence's, not the authority gate's.
    native_fold_mint_bypass::run(|| {
        env.check_decl_readonly(&forged)
            .expect("Extended, reducer allowed: Clean's String.drop proves the equation");
        // The same control over the ENTRY's own environment: a copy of it
        // under `Extended` accepts the equation, so the reducer is present
        // and reachable there and the theory is the one difference.
        let mut extended = k.environment().clone();
        extended.set_kernel_theory(KernelTheory::Extended);
        extended
            .check_decl_readonly(&forged)
            .expect("Extended over the entry's own environment: the reducer fires there");
        let err = k
            .add_checked(forged.clone())
            .expect_err("the entry refuses the disagreement with the gate open");
        assert!(
            matches!(
                err,
                ReferenceRefusal::Kernel(_) | ReferenceRefusal::TheoryExclusion(_)
            ),
            "got {err:?}"
        );
    });
}
