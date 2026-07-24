// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate serialization tests

use crate::cert::*;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;

#[test]
fn test_cert_serialize_json_sort() {
    let cert = ProofCert::Sort {
        level: Level::zero(),
    };

    // Serialize to JSON
    let json = serde_json::to_string(&cert).expect("JSON serialization failed");
    assert!(json.contains("Sort"));

    // Deserialize back
    let restored: ProofCert = serde_json::from_str(&json).expect("JSON deserialization failed");
    assert_eq!(cert, restored);
}

#[test]
fn test_cert_serialize_json_complex() {
    // Build a certificate for λ (x : Prop). x : Prop → Prop
    let prop = Expr::from_kind(ExprKind::Sort(Level::zero()));

    let cert = ProofCert::Lam {
        binder_info: BinderInfo::Default,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_cert: Box::new(ProofCert::BVar {
            idx: 0,
            expected_type: Box::new(prop.clone()),
        }),
        result_type: Box::new(Expr::pi(BinderInfo::Default, prop.clone(), prop.clone())),
    };

    // Serialize to JSON
    let json = serde_json::to_string_pretty(&cert).expect("JSON serialization failed");

    // Deserialize back
    let restored: ProofCert = serde_json::from_str(&json).expect("JSON deserialization failed");
    assert_eq!(cert, restored);
}

#[test]
fn test_cert_serialize_bincode() {
    let cert = ProofCert::Pi {
        binder_info: BinderInfo::Implicit,
        arg_type_cert: Box::new(ProofCert::Sort {
            level: Level::succ(Level::zero()),
        }),
        arg_level: Level::succ(Level::succ(Level::zero())),
        body_type_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        body_level: Level::succ(Level::zero()),
    };

    // Serialize to bincode
    let bytes = bincode::serde::encode_to_vec(&cert, bincode::config::standard())
        .expect("bincode serialization failed");

    // Deserialize back
    let restored: ProofCert =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
            .expect("bincode deserialization failed");
    assert_eq!(cert, restored);
}

#[test]
fn test_def_eq_step_serialize() {
    let step = DefEqStep::Trans(
        Box::new(DefEqStep::Beta),
        Box::new(DefEqStep::Delta(Name::from_string("foo"))),
    );

    // JSON round-trip
    let json = serde_json::to_string(&step).expect("JSON serialization failed");
    let restored: DefEqStep = serde_json::from_str(&json).expect("JSON deserialization failed");
    assert_eq!(step, restored);

    // Bincode round-trip
    let bytes = bincode::serde::encode_to_vec(&step, bincode::config::standard())
        .expect("bincode serialization failed");
    let restored2: DefEqStep =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
            .expect("bincode deserialization failed");
    assert_eq!(step, restored2);
}

#[test]
fn test_cert_serialize_with_mdata() {
    use crate::expr::MDataValue;

    let metadata = vec![(Name::from_string("key"), MDataValue::Bool(true))];
    let cert = ProofCert::MData {
        metadata,
        inner_cert: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        result_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
    };

    // JSON round-trip
    let json = serde_json::to_string(&cert).expect("JSON serialization failed");
    let restored: ProofCert = serde_json::from_str(&json).expect("JSON deserialization failed");
    assert_eq!(cert, restored);
}

#[test]
fn test_cert_serialize_def_eq() {
    let cert = ProofCert::DefEq {
        inner: Box::new(ProofCert::Sort {
            level: Level::zero(),
        }),
        expected_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        actual_type: Box::new(Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero())))),
        eq_steps: vec![DefEqStep::Refl, DefEqStep::Symm(Box::new(DefEqStep::Refl))],
    };

    // JSON round-trip
    let json = serde_json::to_string(&cert).expect("JSON serialization failed");
    let restored: ProofCert = serde_json::from_str(&json).expect("JSON deserialization failed");
    assert_eq!(cert, restored);

    // Bincode round-trip
    let bytes = bincode::serde::encode_to_vec(&cert, bincode::config::standard())
        .expect("bincode serialization failed");
    let restored2: ProofCert =
        bincode::serde::decode_from_slice(&bytes, bincode::config::standard())
            .map(|(__v, _)| __v)
            .expect("bincode deserialization failed");
    assert_eq!(cert, restored2);
}

// ========================================================================
// Proof Replay tests
// ========================================================================
