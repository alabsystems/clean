// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Deep recursion regressions for cert WHNF and def_eq stack safety.

use crate::cert::*;
use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::test_utils::run_with_stack;
use crate::Name;
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

const TINY_STACK: usize = 256 * 1024;

fn empty_env() -> Environment {
    Environment::new()
}

fn deep_let_chain(depth: usize) -> Expr {
    let mut expr = Expr::bvar(0);
    for _ in 0..depth {
        expr = Expr::let_named(Name::anon(), Expr::prop(), Expr::prop(), expr, false);
    }
    expr
}

fn deep_lambda_chain(depth: usize, binder_info: BinderInfo) -> Expr {
    let mut expr = Expr::bvar(0);
    for _ in 0..depth {
        expr = Expr::lam(binder_info, Expr::prop(), expr);
    }
    expr
}

fn deep_def_eq_cert(depth: usize) -> ProofCert {
    let mut cert = ProofCert::Sort {
        level: Level::zero(),
    };
    let sort_type = Expr::from_kind(crate::expr::ExprKind::Sort(Level::succ(Level::zero())));
    for _ in 0..depth {
        cert = ProofCert::DefEq {
            inner: Box::new(cert),
            expected_type: Box::new(sort_type.clone()),
            actual_type: Box::new(sort_type.clone()),
            eq_steps: Vec::new(),
        };
    }
    cert
}

fn deep_def_eq_step(depth: usize) -> DefEqStep {
    let mut step = DefEqStep::Refl;
    for _ in 0..depth {
        step = DefEqStep::Symm(Box::new(step));
    }
    step
}

#[test]
fn test_whnf_deep_let_chain_is_stack_safe() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    let result = verifier.whnf(&deep_let_chain(10_000));

    assert_eq!(result, Expr::prop());
}

#[test]
fn test_def_eq_deep_lambda_chain_is_stack_safe() {
    let env = empty_env();
    let verifier = CertVerifier::new(&env);

    assert!(verifier.def_eq(
        &deep_lambda_chain(10_000, BinderInfo::Default),
        &deep_lambda_chain(10_000, BinderInfo::Implicit),
    ));
}

/// Regression: `replay_cert` was not stack-safe (no `stack_safe` wrapper),
/// while the verifier's `verify()` was. A deeply nested certificate tree
/// could cause stack overflow during replay.
#[test]
fn test_replay_cert_deep_def_eq_chain_is_stack_safe() {
    // Build a deeply nested cert: DefEq { inner: DefEq { inner: ... Sort } }
    let cert = deep_def_eq_cert(10_000);

    // This should not stack overflow
    let result = replay_cert(&cert);
    assert_eq!(
        result,
        Expr::from_kind(crate::expr::ExprKind::Sort(Level::zero()))
    );
}

/// The Pi/Let replay paths use `extract_type_from_sort_cert`, so protecting
/// only ordinary replay recursion is insufficient. Exercise the helper with
/// the same adversarial depth through the public replay API.
#[test]
fn test_replay_cert_deep_sort_extraction_is_stack_safe() {
    let prop = Expr::from_kind(crate::expr::ExprKind::Sort(Level::zero()));
    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(deep_def_eq_cert(10_000)),
        arg_level: Level::succ(Level::zero()),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_level: Level::succ(Level::zero()),
    };

    assert_eq!(
        replay_cert(&cert),
        Expr::pi(BinderInfo::Default, prop.clone(), prop)
    );
}

/// Regression: the Arc-identity inference memo clones a retained certificate
/// after returning from a recursive inference call. The derived `Clone`
/// implementation had no stack-growth boundary of its own, so a clone begun
/// near the guard page could SIGBUS the entire process on the default test
/// thread stack.
#[test]
fn test_clone_deep_proof_cert_is_stack_safe() {
    let cert = deep_def_eq_cert(10_000);
    let cloned = cert.clone();

    let mut depth = 0;
    let mut cursor = &cloned;
    while let ProofCert::DefEq { inner, .. } = cursor {
        depth += 1;
        cursor = inner;
    }
    assert_eq!(depth, 10_000);
}

/// `DefEqStep` is a recursive tree independent of the enclosing certificate,
/// so it needs the same per-child clone boundary.
#[test]
fn test_clone_deep_def_eq_step_is_stack_safe() {
    let step = deep_def_eq_step(10_000);

    let cloned = step.clone();
    let mut depth = 0;
    let mut cursor = &cloned;
    while let DefEqStep::Symm(inner) = cursor {
        depth += 1;
        cursor = inner;
    }
    assert_eq!(depth, 10_000);
}

#[test]
fn recursive_kernel_values_survive_traits_serde_and_natural_drop_on_tiny_stack() {
    run_with_stack(TINY_STACK, || {
        let mut name = Name::anon();
        let mut level = Level::zero();
        for _ in 0..20_000 {
            name = name.str("segment");
            level = Level::succ(level);
        }

        let name_clone = name.clone();
        let level_clone = level.clone();
        assert_eq!(name, name_clone);
        assert_eq!(level, level_clone);

        let mut name_hash = DefaultHasher::new();
        name.hash(&mut name_hash);
        let mut name_clone_hash = DefaultHasher::new();
        name_clone.hash(&mut name_clone_hash);
        assert_eq!(name_hash.finish(), name_clone_hash.finish());

        let mut level_hash = DefaultHasher::new();
        level.hash(&mut level_hash);
        let mut level_clone_hash = DefaultHasher::new();
        level_clone.hash(&mut level_clone_hash);
        assert_eq!(level_hash.finish(), level_clone_hash.finish());

        assert!(format!("{name:?}").len() < 512);
        assert!(format!("{level:?}").len() < 512);

        let name_bytes =
            bincode::serde::encode_to_vec(&name, bincode::config::standard()).expect("name encode");
        let (name_roundtrip, _): (Name, usize) =
            bincode::serde::decode_from_slice(&name_bytes, bincode::config::standard())
                .expect("name decode");
        assert_eq!(name, name_roundtrip);

        let level_bytes = bincode::serde::encode_to_vec(&level, bincode::config::standard())
            .expect("level encode");
        let (level_roundtrip, _): (Level, usize) =
            bincode::serde::decode_from_slice(&level_bytes, bincode::config::standard())
                .expect("level decode");
        assert_eq!(level, level_roundtrip);

        let cert = deep_def_eq_cert(10_000);
        let cert_clone = cert.clone();
        assert_eq!(cert, cert_clone);
        assert!(format!("{cert:?}").len() < 1_024);
        let cert_bytes =
            bincode::serde::encode_to_vec(&cert, bincode::config::standard()).expect("cert encode");
        let (cert_roundtrip, _): (ProofCert, usize) =
            bincode::serde::decode_from_slice(&cert_bytes, bincode::config::standard())
                .expect("cert decode");
        assert_eq!(cert, cert_roundtrip);

        let step = deep_def_eq_step(20_000);
        let step_clone = step.clone();
        assert_eq!(step, step_clone);
        assert!(format!("{step:?}").len() < 512);
        let step_bytes =
            bincode::serde::encode_to_vec(&step, bincode::config::standard()).expect("step encode");
        let (step_roundtrip, _): (DefEqStep, usize) =
            bincode::serde::decode_from_slice(&step_bytes, bincode::config::standard())
                .expect("step decode");
        assert_eq!(step, step_roundtrip);

        // All values are intentionally destroyed normally on this 256 KiB
        // thread. This is the regression for recursive destructor safety.
    });
}

#[test]
fn bounded_debug_preserves_shallow_certificate_metadata() {
    use crate::expr::MDataValue;

    assert_eq!(
        format!(
            "{:?}",
            ProofCert::BVar {
                idx: 7,
                expected_type: Box::new(Expr::prop()),
            }
        ),
        "BVar { idx: 7, expected_type: Sort }"
    );
    assert_eq!(
        format!("{:?}", DefEqStep::Symm(Box::new(DefEqStep::Refl))),
        "Symm(Refl)"
    );
    assert_eq!(format!("{:?}", Level::succ(Level::zero())), "Succ(Zero)");

    let cert = ProofCert::MData {
        metadata: vec![(
            Name::from_string("diagnostic.flag"),
            MDataValue::String("abcdefghijklmnopqrstuvwxyz0123456789-tail".into()),
        )],
        inner_cert: Box::new(ProofCert::BVar {
            idx: 7,
            expected_type: Box::new(Expr::prop()),
        }),
        result_type: Box::new(Expr::prop()),
    };
    let output = format!("{cert:?}");
    assert!(output.contains("MData"));
    assert!(output.contains("diagnostic"));
    assert!(output.contains("first_value_kind: \"String\""));
    assert!(output.contains("len: 41"));
    assert!(output.contains("abcdefghijklmnopqrstuvwxyz012345"));
    assert!(output.contains("inner_cert: BVar"));
    assert!(output.len() < 1_024);

    let step = DefEqStep::Struct(
        "a-structural-step-label-that-is-deliberately-long".repeat(8),
        vec![DefEqStep::Delta(Name::from_string("Demo.delta"))],
    );
    let step_output = format!("{step:?}");
    assert!(step_output.contains("Struct"));
    assert!(step_output.contains("len: 1"));
    assert!(step_output.contains("first: Delta"));
    assert!(step_output.len() < 512);
}
