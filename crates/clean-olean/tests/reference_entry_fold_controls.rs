// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR0 test 1's `Extended` control, in its own binary because it needs the
//! native-fold authority bypass, which is process-global. It lives in
//! `clean-olean` because that crate's dev-dependency edge enables
//! `clean-kernel/test-fixtures`, the feature the bypass is compiled under;
//! the rest of the KR0 suite is `crates/clean-kernel/tests/reference_entry.rs`.
//!
//! The plan's control reads "accepted under `KernelTheory::Extended`".
//! Measured on Clean HEAD: native-fold authority (`native_fold_authority.rs`,
//! 2026-09-26) refuses the host-answering platform reducer in EVERY theory,
//! because an opaque extern has no definition a fold could be justified by, so
//! `Extended` no longer accepts `isOSX = true` on its own. The control
//! therefore opens the authority gate (`native_fold_mint_bypass`) and shows
//! the two halves the fence depends on: with the reducer allowed to fire,
//! `Extended` decides the platform boolean by the BUILD HOST — the term is
//! exactly one an extra-Lean reducer decides — and the reference entry still
//! refuses both spellings, because its theory never fires that reducer.

use clean_kernel::env::{native_fold_mint_bypass, KernelTheory, LeanTheoryExclusion};
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceKernel, ReferenceRefusal,
};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn platform_env() -> Environment {
    let mut env = Environment::with_prelude();
    let unit = c("Unit");
    env.add_decl(Declaration::Opaque {
        name: name("System.Platform.getIsOSX"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, unit.clone(), c("Bool")),
        value: Expr::lam(BinderInfo::Default, unit, c("Bool.false")),
    })
    .expect("opaque getIsOSX");
    env.add_decl(Declaration::Definition {
        name: name("System.Platform.isOSX"),
        level_params: vec![],
        type_: c("Bool"),
        value: Expr::app(c("System.Platform.getIsOSX"), c("Unit.unit")),
        is_reducible: false,
    })
    .expect("def isOSX");
    env
}

fn is_osx_is(b: bool) -> Declaration {
    let lit = c(if b { "Bool.true" } else { "Bool.false" });
    let one = || vec![Level::succ(Level::zero())];
    Declaration::Theorem {
        name: name(if b {
            "kr0_is_osx_true"
        } else {
            "kr0_is_osx_false"
        }),
        level_params: vec![],
        type_: Expr::apps(
            Expr::const_(name("Eq"), one()),
            [c("Bool"), c("System.Platform.isOSX"), lit.clone()],
        ),
        value: Expr::apps(Expr::const_(name("Eq.refl"), one()), [c("Bool"), lit]),
    }
}

#[test]
fn test_is_osx_extended_decides_by_host_and_the_entry_refuses_both() {
    let host_is_osx = cfg!(target_os = "macos");
    // Without the bypass, Extended refuses both spellings (authority).
    let env = platform_env();
    assert_eq!(env.kernel_theory(), KernelTheory::Extended);
    for b in [true, false] {
        assert!(
            env.check_decl_readonly(&is_osx_is(b)).is_err(),
            "authority closes isOSX = {b} in Extended"
        );
    }
    native_fold_mint_bypass::run(|| {
        let env = platform_env();
        // Extended, reducer allowed: the host's answer is accepted, the
        // other spelling refused.
        env.check_decl_readonly(&is_osx_is(host_is_osx))
            .expect("Extended decides isOSX by the build host once the reducer may fire");
        assert!(env.check_decl_readonly(&is_osx_is(!host_is_osx)).is_err());
        // The entry refuses both, gate open or not.
        let mut k = ReferenceKernel::new(platform_env()).expect("platform base");
        for b in [true, false] {
            let err = k.add_checked(is_osx_is(b)).expect_err("the fence refuses");
            assert!(
                matches!(
                    err,
                    ReferenceRefusal::TheoryExclusion(LeanTheoryExclusion::OpaqueExternFamily)
                ),
                "isOSX = {b}: got {err:?}"
            );
        }
    });
}
