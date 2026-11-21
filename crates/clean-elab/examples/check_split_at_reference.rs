// Copyright 2026 Andrew Yates. Apache-2.0.
//! Recheck actual native tactic proofs in an independently replayed original core.
//! Usage: check_split_at_reference LEAN_LIBRARY_DIRECTORY
//! The native prelude is not claimed to be the pinned original core. Its raw
//! dependency replay refusal is preserved separately; no binding table is changed.

use clean_elab::elaborate_decl_and_register_with_warning;
use clean_kernel::{
    expr::UsedConstants, BinderInfo, Environment, Expr, KernelEnvError, KernelTypeError, Level,
    Name, ReferenceRefusal,
};
use clean_olean::{load_module_with_deps, reference_base_closed, ClosedRecheckOptions};
use std::collections::{BTreeSet, HashSet};
use std::path::PathBuf;

#[path = "../src/tests_split_at_source.rs"]
mod cases;

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn conditional(p: u32, instance: u32) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [
            Expr::prop(),
            Expr::bvar(p),
            Expr::bvar(instance),
            constant("True"),
            constant("False"),
        ],
    )
}

/// Independently quoted fixture statements. The expected goal is never taken
/// from the native elaborator's proposed theorem type.
fn expected_goal(dependent: bool, wrong: bool) -> Expr {
    let p = Expr::bvar(if dependent { 3 } else { 2 });
    let mut conclusion = if wrong {
        Expr::arrow(p, constant("False"))
    } else {
        p
    };
    if dependent {
        let equality = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::zero()]),
            [conditional(2, 1), Expr::bvar(0), Expr::bvar(0)],
        );
        conclusion = Expr::pi(BinderInfo::Default, equality, conclusion);
    }
    Expr::pi(
        BinderInfo::Default,
        Expr::prop(),
        Expr::pi(
            BinderInfo::InstImplicit,
            Expr::app(constant("Decidable"), Expr::bvar(0)),
            Expr::pi(BinderInfo::Default, conditional(1, 0), conclusion),
        ),
    )
}

fn boolean_match(major: u32) -> Expr {
    Expr::apps(
        Expr::const_(
            Name::from_string("Bool.rec"),
            vec![Level::succ(Level::zero())],
        ),
        [
            Expr::lam(BinderInfo::Default, constant("Bool"), Expr::prop()),
            constant("False"),
            constant("True"),
            Expr::bvar(major),
        ],
    )
}

/// A separate, fixed Bool.rec quotation of the match fixtures. Neither the
/// expected match type nor the wrong Boolean result comes from the proposer.
fn expected_match_goal(dependent: bool, wrong: bool) -> Expr {
    let mut conclusion = Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [
            constant("Bool"),
            Expr::bvar(if dependent { 2 } else { 1 }),
            constant(if wrong { "Bool.false" } else { "Bool.true" }),
        ],
    );
    if dependent {
        let equality = Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![Level::zero()]),
            [boolean_match(1), Expr::bvar(0), Expr::bvar(0)],
        );
        conclusion = Expr::pi(BinderInfo::Default, equality, conclusion);
    }
    Expr::pi(
        BinderInfo::Default,
        constant("Bool"),
        Expr::pi(BinderInfo::Default, boolean_match(0), conclusion),
    )
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments = std::env::args_os().skip(1);
    let library = PathBuf::from(
        arguments
            .next()
            .ok_or("supply the original Lean library directory")?,
    );
    if arguments.next().is_some() {
        return Err("expected exactly one Lean library directory".into());
    }
    let mut original = Environment::for_lean_replay();
    load_module_with_deps(&mut original, "Init.SimpLemmas", &[library])?;
    let mut proofs = Vec::new();
    let mut constants = HashSet::new();
    let fixtures = cases::POSITIVE
        .into_iter()
        .enumerate()
        .map(|(index, fixture)| {
            (
                fixture,
                expected_goal(index == 1, false),
                expected_goal(index == 1, true),
            )
        })
        .chain(
            cases::MATCH_POSITIVE
                .into_iter()
                .enumerate()
                .map(|(index, fixture)| {
                    (
                        fixture,
                        expected_match_goal(index == 1, false),
                        expected_match_goal(index == 1, true),
                    )
                }),
        );
    for ((name, source), goal, wrong_goal) in fixtures {
        let native = cases::elaborate(source)?;
        let declaration = native
            .get_const(&Name::from_string(name))
            .ok_or("missing native theorem")?;
        let proof = declaration
            .value
            .clone()
            .ok_or("native theorem has no proof")?;
        goal.used_constants_dag(UsedConstants::WithProjectionStructures, &mut constants);
        wrong_goal.used_constants_dag(UsedConstants::WithProjectionStructures, &mut constants);
        proof.used_constants_dag(UsedConstants::WithProjectionStructures, &mut constants);
        proofs.push((name, goal, wrong_goal, proof));
    }
    constants.insert(Name::from_string("False"));
    let roots: BTreeSet<_> = constants.into_iter().collect();
    let replay = reference_base_closed(&original, &roots, &ClosedRecheckOptions::default())?;
    eprintln!(
        "original core: roots={}, admitted={}, axioms={:?}",
        roots.len(),
        replay.admitted.len(),
        replay.report.axioms_admitted
    );
    let kernel = replay
        .into_kernel()
        .map_err(|report| format!("{report:#?}"))?;
    for (name, ty, wrong, proof) in proofs {
        kernel.check_closed_term(&ty, &proof)?;
        match kernel.check_closed_term(&wrong, &proof) {
            Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
                source: KernelTypeError::TypeMismatch { .. },
                ..
            })) => eprintln!("{name}: original positive accepted; actual wrong-goal TypeMismatch"),
            result => {
                return Err(
                    format!("{name}: expected actual kernel TypeMismatch, got {result:?}").into(),
                )
            }
        }
    }
    for source in cases::NEGATIVE.into_iter().chain(cases::MATCH_NEGATIVE) {
        if cases::elaborate(source).is_ok() {
            return Err("a negative source fixture was accepted".into());
        }
    }
    Ok(())
}
