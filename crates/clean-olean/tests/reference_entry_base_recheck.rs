// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! KR1 increment 3 (`docs/DECISIONS.md` R143): the reference entry re-checks
//! the constants `new`'s base hands it. In its own binary because it opens the
//! native-fold authority bypass, which is process-global (the same reason
//! `reference_entry_fold_controls.rs` is alone: a test asserting the gate is
//! closed must not run beside this one).

use clean_kernel::env::native_fold_mint_bypass;
use clean_kernel::{
    BinderInfo, Declaration, Environment, Expr, Level, Name, ReferenceKernel, ReferenceRefusal,
};

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

/// As `reference_entry_fold_controls.rs`: a `with_prelude` base with the
/// platform opaque and `isOSX` over it.
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

/// KR1 increment 3 (R143), R107's first "not fenced" limit: a base constant's
/// `FullKernelCheck` stamp says it passed the kernel in the theory it was
/// added under, not in the entry's. Here the base admits `isOSX = <host>`
/// under `Extended` with the platform reducer allowed to fire, so the stamp
/// is real and `new` takes the base. Measured on `1da954169` (before R143):
/// a theorem citing that base constant was accepted through the entry
/// (`Ok(LeanReferenceV1)`), although the entry refuses the same statement
/// stated directly. Now a cited base constant is re-checked in the entry's
/// theory first, and refuses as `BaseRecheck` naming it, on both paths.
/// Control: a citation of a base constant that re-checks (`Eq.refl`) is
/// accepted over the same entry.
#[test]
fn test_a_base_stamp_earned_under_extended_is_rechecked_at_citation() {
    let host_is_osx = cfg!(target_os = "macos");
    native_fold_mint_bypass::run(|| {
        let mut base = platform_env();
        base.add_decl(is_osx_is(host_is_osx))
            .expect("Extended admits the host's answer with the reducer allowed");
        let host = name(if host_is_osx {
            "kr0_is_osx_true"
        } else {
            "kr0_is_osx_false"
        });
        let stated = match is_osx_is(host_is_osx) {
            Declaration::Theorem { type_, .. } => type_,
            _ => unreachable!(),
        };
        let mut k = ReferenceKernel::new(base).expect("the stamp is FullKernelCheck");
        let citer = Declaration::Theorem {
            name: name("kr3_cites_host_answer"),
            level_params: vec![],
            type_: stated.clone(),
            value: Expr::const_(host.clone(), vec![]),
        };
        match k.add_checked(citer) {
            Err(ReferenceRefusal::BaseRecheck { decl, .. }) => assert_eq!(decl, host),
            other => panic!("add_checked: expected BaseRecheck of {host}, got {other:?}"),
        }
        match k.check_closed_term(&stated, &Expr::const_(host.clone(), vec![])) {
            Err(ReferenceRefusal::BaseRecheck { decl, .. }) => assert_eq!(decl, host),
            other => panic!("check_closed_term: expected BaseRecheck of {host}, got {other:?}"),
        }
        // Control.
        let one = || vec![Level::succ(Level::zero())];
        let t = c("Bool.true");
        k.add_checked(Declaration::Theorem {
            name: name("kr3_refl_control"),
            level_params: vec![],
            type_: Expr::apps(
                Expr::const_(name("Eq"), one()),
                [c("Bool"), t.clone(), t.clone()],
            ),
            value: Expr::apps(Expr::const_(name("Eq.refl"), one()), [c("Bool"), t]),
        })
        .expect("control: a citation of base constants that re-check");
    });
}

/// Review of R143 (B1): the re-check covers the cited constant's whole base
/// closure, not only the constant cited. Here the Extended-earned stamp is
/// one level down: the base's `kr3_wrapper : isOSX = <host> := <host stamp>`
/// re-checks on its own (it cites a resident theorem of the right type), so
/// only a re-check of what it cites refuses. Before this test, a mutant that
/// re-checked the cited root alone passed every test. Control: the wrapper
/// re-checks once its cited stamp is a theorem the entry's theory proves
/// (`Eq.refl` at `Bool.true = Bool.true`, wrapped the same way).
#[test]
fn test_a_wrapped_extended_stamp_is_rechecked_through_its_closure() {
    let host_is_osx = cfg!(target_os = "macos");
    native_fold_mint_bypass::run(|| {
        let mut base = platform_env();
        base.add_decl(is_osx_is(host_is_osx))
            .expect("Extended admits the host's answer with the reducer allowed");
        let host = name(if host_is_osx {
            "kr0_is_osx_true"
        } else {
            "kr0_is_osx_false"
        });
        let stated = match is_osx_is(host_is_osx) {
            Declaration::Theorem { type_, .. } => type_,
            _ => unreachable!(),
        };
        base.add_decl(Declaration::Theorem {
            name: name("kr3_wrapper"),
            level_params: vec![],
            type_: stated.clone(),
            value: Expr::const_(host.clone(), vec![]),
        })
        .expect("a theorem resting on the host stamp");
        let one = || vec![Level::succ(Level::zero())];
        let t = c("Bool.true");
        let refl_ty = Expr::apps(
            Expr::const_(name("Eq"), one()),
            [c("Bool"), t.clone(), t.clone()],
        );
        base.add_decl(Declaration::Theorem {
            name: name("kr3_refl_inner"),
            level_params: vec![],
            type_: refl_ty.clone(),
            value: Expr::apps(Expr::const_(name("Eq.refl"), one()), [c("Bool"), t]),
        })
        .expect("refl inner");
        base.add_decl(Declaration::Theorem {
            name: name("kr3_refl_wrapper"),
            level_params: vec![],
            type_: refl_ty.clone(),
            value: c("kr3_refl_inner"),
        })
        .expect("refl wrapper");
        let k = ReferenceKernel::new(base).expect("the stamps are FullKernelCheck");
        match k.check_closed_term(&stated, &c("kr3_wrapper")) {
            Err(ReferenceRefusal::BaseRecheck { decl, .. }) => assert_eq!(decl, host),
            other => panic!("expected BaseRecheck of {host} via the wrapper, got {other:?}"),
        }
        k.check_closed_term(&refl_ty, &c("kr3_refl_wrapper"))
            .expect("control: a wrapper over a stamp that re-checks");
    });
}
