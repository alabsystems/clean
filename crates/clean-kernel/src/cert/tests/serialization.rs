// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Certificate serialization tests

use crate::cert::*;
use crate::expr::{BinderInfo, Expr, ExprKind, FVarId, Literal, MDataValue};
use crate::level::Level;
use crate::name::Name;
use sha2::{Digest, Sha256};
use std::sync::Arc;

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

fn leaf() -> Box<ProofCert> {
    Box::new(ProofCert::SProp)
}

fn all_proof_cert_wire_fixtures() -> Vec<(&'static str, ProofCert)> {
    let prop = || Box::new(Expr::prop());
    let level0 = || Level::zero();
    let level1 = || Level::succ(Level::zero());
    let name = || Name::from_string("Wire.fixture");

    let mut fixtures = vec![
        ("Sort", ProofCert::Sort { level: level1() }),
        (
            "BVar",
            ProofCert::BVar {
                idx: 7,
                expected_type: prop(),
            },
        ),
        (
            "FVar",
            ProofCert::FVar {
                id: FVarId::new(17),
                type_: prop(),
            },
        ),
        (
            "Const",
            ProofCert::Const {
                name: name(),
                levels: vec![level0(), Level::param(Name::from_string("u"))],
                type_: prop(),
            },
        ),
        (
            "App",
            ProofCert::App {
                fn_cert: leaf(),
                fn_type: prop(),
                arg_cert: leaf(),
                result_type: prop(),
            },
        ),
        (
            "Lam",
            ProofCert::Lam {
                binder_info: BinderInfo::StrictImplicit,
                arg_type_cert: leaf(),
                body_cert: leaf(),
                result_type: prop(),
            },
        ),
        (
            "Pi",
            ProofCert::Pi {
                binder_info: BinderInfo::InstImplicit,
                arg_type_cert: leaf(),
                arg_level: level1(),
                body_type_cert: leaf(),
                body_level: Level::param(Name::from_string("v")),
            },
        ),
        (
            "Let",
            ProofCert::Let {
                type_cert: leaf(),
                value_cert: leaf(),
                body_cert: leaf(),
                result_type: prop(),
            },
        ),
        (
            "Lit.Nat",
            ProofCert::Lit {
                lit: Literal::nat(42),
                type_: prop(),
            },
        ),
        (
            "Lit.String",
            ProofCert::Lit {
                lit: Literal::String(Arc::from("wire")),
                type_: prop(),
            },
        ),
        (
            "DefEq",
            ProofCert::DefEq {
                inner: leaf(),
                expected_type: prop(),
                actual_type: prop(),
                eq_steps: vec![
                    DefEqStep::Refl,
                    DefEqStep::Delta(Name::from_string("Wire.delta")),
                ],
            },
        ),
        (
            "MData",
            ProofCert::MData {
                metadata: vec![
                    (Name::from_string("bool"), MDataValue::Bool(true)),
                    (Name::from_string("nat"), MDataValue::Nat(99)),
                    (
                        Name::from_string("string"),
                        MDataValue::String(Arc::from("metadata")),
                    ),
                    (
                        Name::from_string("name"),
                        MDataValue::Name(Name::from_string("Wire.metadata")),
                    ),
                ],
                inner_cert: leaf(),
                result_type: prop(),
            },
        ),
        (
            "Proj",
            ProofCert::Proj {
                struct_name: Name::from_string("Wire.Struct"),
                idx: 3,
                expr_cert: leaf(),
                expr_type: prop(),
                field_type: prop(),
            },
        ),
        ("CubicalInterval", ProofCert::CubicalInterval),
        (
            "CubicalEndpoint",
            ProofCert::CubicalEndpoint { is_one: true },
        ),
        (
            "CubicalPath",
            ProofCert::CubicalPath {
                ty_cert: leaf(),
                ty_level: level1(),
                left_cert: leaf(),
                right_cert: leaf(),
            },
        ),
        (
            "CubicalPathLam",
            ProofCert::CubicalPathLam {
                body_cert: leaf(),
                body_type: prop(),
                result_type: prop(),
            },
        ),
        (
            "CubicalPathApp",
            ProofCert::CubicalPathApp {
                path_cert: leaf(),
                arg_cert: leaf(),
                path_type: prop(),
                result_type: prop(),
            },
        ),
        (
            "CubicalHComp",
            ProofCert::CubicalHComp {
                ty_cert: leaf(),
                phi_cert: leaf(),
                u_cert: leaf(),
                base_cert: leaf(),
                result_type: prop(),
            },
        ),
        (
            "CubicalTransp",
            ProofCert::CubicalTransp {
                ty_cert: leaf(),
                phi_cert: leaf(),
                base_cert: leaf(),
                result_type: prop(),
            },
        ),
        (
            "CubicalCoe",
            ProofCert::CubicalCoe {
                ty_cert: leaf(),
                r_cert: leaf(),
                s_cert: leaf(),
                base_cert: leaf(),
                result_type: prop(),
            },
        ),
        (
            "ZFCMem",
            ProofCert::ZFCMem {
                elem_cert: leaf(),
                set_cert: leaf(),
            },
        ),
        (
            "ZFCComprehension",
            ProofCert::ZFCComprehension {
                var_ty_cert: leaf(),
                pred_cert: leaf(),
                result_type: prop(),
            },
        ),
        ("SProp", ProofCert::SProp),
        ("Squash", ProofCert::Squash { inner_cert: leaf() }),
    ];

    let zfc_kinds = [
        ("Empty", ZFCSetCertKind::Empty),
        ("Singleton", ZFCSetCertKind::Singleton(leaf())),
        ("Pair", ZFCSetCertKind::Pair(leaf(), leaf())),
        ("Union", ZFCSetCertKind::Union(leaf())),
        ("PowerSet", ZFCSetCertKind::PowerSet(leaf())),
        (
            "Separation",
            ZFCSetCertKind::Separation {
                set_cert: leaf(),
                pred_cert: leaf(),
            },
        ),
        (
            "Replacement",
            ZFCSetCertKind::Replacement {
                set_cert: leaf(),
                func_cert: leaf(),
            },
        ),
        ("Infinity", ZFCSetCertKind::Infinity),
        ("Choice", ZFCSetCertKind::Choice(leaf())),
    ];
    fixtures.extend(zfc_kinds.into_iter().map(|(kind_name, kind)| {
        (
            match kind_name {
                "Empty" => "ZFCSet.Empty",
                "Singleton" => "ZFCSet.Singleton",
                "Pair" => "ZFCSet.Pair",
                "Union" => "ZFCSet.Union",
                "PowerSet" => "ZFCSet.PowerSet",
                "Separation" => "ZFCSet.Separation",
                "Replacement" => "ZFCSet.Replacement",
                "Infinity" => "ZFCSet.Infinity",
                "Choice" => "ZFCSet.Choice",
                _ => unreachable!(),
            },
            ProofCert::ZFCSet {
                kind,
                result_type: prop(),
            },
        )
    }));
    fixtures
}

fn all_def_eq_step_wire_fixtures() -> Vec<(&'static str, DefEqStep)> {
    vec![
        ("Refl", DefEqStep::Refl),
        ("Symm", DefEqStep::Symm(Box::new(DefEqStep::Refl))),
        (
            "Trans",
            DefEqStep::Trans(Box::new(DefEqStep::Beta), Box::new(DefEqStep::Zeta)),
        ),
        ("Beta", DefEqStep::Beta),
        ("Delta", DefEqStep::Delta(Name::from_string("Wire.delta"))),
        ("Zeta", DefEqStep::Zeta),
        ("Iota", DefEqStep::Iota),
        (
            "Struct",
            DefEqStep::Struct(
                "congruence".to_owned(),
                vec![DefEqStep::Refl, DefEqStep::Beta],
            ),
        ),
    ]
}

fn level_wire_fixtures() -> Vec<Level> {
    vec![
        Level::Zero,
        Level::Succ(Arc::new(Level::Zero).into()),
        Level::Max(
            Arc::new(Level::param(Name::from_string("u"))).into(),
            Arc::new(Level::param(Name::from_string("v"))).into(),
        ),
        Level::IMax(
            Arc::new(Level::param(Name::from_string("w"))).into(),
            Arc::new(Level::param(Name::from_string("x"))).into(),
        ),
        Level::Param(Name::from_string("p")),
    ]
}

fn name_wire_fixtures() -> Vec<Name> {
    vec![
        Name::anon(),
        Name::anon().str("root"),
        Name::anon().num(12),
        Name::anon().str("Root").num(9).str("leaf"),
    ]
}

fn digest_len_prefixed<'a>(values: impl IntoIterator<Item = &'a [u8]>) -> String {
    let mut hasher = Sha256::new();
    for value in values {
        hasher.update((value.len() as u64).to_le_bytes());
        hasher.update(value);
    }
    hasher
        .finalize()
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn exact_wire_digests<T: serde::Serialize>(values: &[T]) -> (String, String) {
    let json: Vec<Vec<u8>> = values
        .iter()
        .map(|value| serde_json::to_vec(value).expect("fixture JSON encode"))
        .collect();
    let bincode: Vec<Vec<u8>> = values
        .iter()
        .map(|value| {
            bincode::serde::encode_to_vec(value, bincode::config::standard())
                .expect("fixture bincode encode")
        })
        .collect();
    (
        digest_len_prefixed(json.iter().map(Vec::as_slice)),
        digest_len_prefixed(bincode.iter().map(Vec::as_slice)),
    )
}

#[test]
fn manual_recursive_serde_preserves_every_certificate_wire_variant() {
    let fixtures = all_proof_cert_wire_fixtures();
    assert_eq!(
        fixtures.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
        [
            "Sort",
            "BVar",
            "FVar",
            "Const",
            "App",
            "Lam",
            "Pi",
            "Let",
            "Lit.Nat",
            "Lit.String",
            "DefEq",
            "MData",
            "Proj",
            "CubicalInterval",
            "CubicalEndpoint",
            "CubicalPath",
            "CubicalPathLam",
            "CubicalPathApp",
            "CubicalHComp",
            "CubicalTransp",
            "CubicalCoe",
            "ZFCMem",
            "ZFCComprehension",
            "SProp",
            "Squash",
            "ZFCSet.Empty",
            "ZFCSet.Singleton",
            "ZFCSet.Pair",
            "ZFCSet.Union",
            "ZFCSet.PowerSet",
            "ZFCSet.Separation",
            "ZFCSet.Replacement",
            "ZFCSet.Infinity",
            "ZFCSet.Choice",
        ]
    );

    for (name, cert) in &fixtures {
        let json = serde_json::to_vec(cert).expect("fixture JSON encode");
        let json_roundtrip: ProofCert =
            serde_json::from_slice(&json).unwrap_or_else(|error| panic!("{name} JSON: {error}"));
        assert_eq!(cert, &json_roundtrip, "{name} JSON round-trip");

        let bincode = bincode::serde::encode_to_vec(cert, bincode::config::standard())
            .expect("fixture bincode encode");
        let (bincode_roundtrip, _): (ProofCert, usize) =
            bincode::serde::decode_from_slice(&bincode, bincode::config::standard())
                .unwrap_or_else(|error| panic!("{name} bincode: {error}"));
        assert_eq!(cert, &bincode_roundtrip, "{name} bincode round-trip");
    }

    let values: Vec<_> = fixtures.iter().map(|(_, cert)| cert).collect();
    // These constants were generated by running these exact fixtures against
    // pre-hardening commit 362449cde, where ProofCert still used derived serde.
    let digests = exact_wire_digests(&values);
    assert_eq!(
        digests,
        (
            "fbe60ecd9a2cf0a9b30d275f1496b6c26e475af2315e1ec3c1cb56bcd2d1473b".to_owned(),
            "70646ce4a1ec18a23a6c8db2a93d380e53222ec657e9ea4c6caea16723924544".to_owned(),
        ),
        "length-prefixed aggregate is an exact golden of every fixture"
    );
}

#[test]
fn manual_recursive_serde_preserves_every_def_eq_wire_variant() {
    let fixtures = all_def_eq_step_wire_fixtures();
    assert_eq!(
        fixtures.iter().map(|(name, _)| *name).collect::<Vec<_>>(),
        ["Refl", "Symm", "Trans", "Beta", "Delta", "Zeta", "Iota", "Struct"]
    );

    for (name, step) in &fixtures {
        let json = serde_json::to_vec(step).expect("fixture JSON encode");
        let json_roundtrip: DefEqStep =
            serde_json::from_slice(&json).unwrap_or_else(|error| panic!("{name} JSON: {error}"));
        assert_eq!(step, &json_roundtrip, "{name} JSON round-trip");

        let bincode = bincode::serde::encode_to_vec(step, bincode::config::standard())
            .expect("fixture bincode encode");
        let (bincode_roundtrip, _): (DefEqStep, usize) =
            bincode::serde::decode_from_slice(&bincode, bincode::config::standard())
                .unwrap_or_else(|error| panic!("{name} bincode: {error}"));
        assert_eq!(step, &bincode_roundtrip, "{name} bincode round-trip");
    }

    let values: Vec<_> = fixtures.iter().map(|(_, step)| step).collect();
    // Provenance: pre-hardening commit 362449cde's derived DefEqStep serde.
    let digests = exact_wire_digests(&values);
    assert_eq!(
        digests,
        (
            "ad43800bbc408086d0cf75198e5e4dc7bc6c33efe13008121ef31f33f0b6706e".to_owned(),
            "37b9e029725c6d28ac20dbc5ecf109bbb833dcde3eeea460a85fc46dfb7ccd01".to_owned(),
        ),
        "length-prefixed aggregate is an exact golden of every fixture"
    );
}

#[test]
fn level_and_name_manual_serde_preserve_pre_change_wire_bytes() {
    // Provenance: pre-hardening commit 362449cde's derived Level/Name serde.
    let level_digests = exact_wire_digests(&level_wire_fixtures());
    assert_eq!(
        level_digests,
        (
            "08b20599c09b533948df869f0a4695d495f777fb9210783d50f3581c1865dc22".to_owned(),
            "95448330a8df8aeeb64130a02d34bce3653803a7f225f2ef4884f908469f9d65".to_owned(),
        )
    );

    let name_digests = exact_wire_digests(&name_wire_fixtures());
    assert_eq!(
        name_digests,
        (
            "5d4817e77bed894ace5ff39cb44888ecafe9e84dd565d00239620b0e54145a55".to_owned(),
            "9b472faebe7209d7fcbb52dd8eacb0272047227333d4eeabcd0409f4a2657c4b".to_owned(),
        )
    );
}

fn deep_cert(depth: usize) -> ProofCert {
    let mut cert = ProofCert::SProp;
    for _ in 0..depth {
        cert = ProofCert::Squash {
            inner_cert: Box::new(cert),
        };
    }
    cert
}

fn deep_step(depth: usize) -> DefEqStep {
    let mut step = DefEqStep::Refl;
    for _ in 0..depth {
        step = DefEqStep::Symm(Box::new(step));
    }
    step
}

#[test]
fn certificate_decode_depth_limits_fail_closed() {
    let cert = deep_cert(128);
    let cert_json = serde_json::to_vec(&cert).unwrap();
    let cert_json_error = crate::with_decode_resource_limits(
        crate::DecodeResourceLimits {
            max_nodes: 1_000,
            max_depth: 32,
        },
        || serde_json::from_slice::<ProofCert>(&cert_json),
    )
    .expect_err("deep JSON certificate must fail inside the scoped decoder");
    assert!(cert_json_error.to_string().contains("structural depth"));

    let cert_bytes = bincode::serde::encode_to_vec(&cert, bincode::config::standard()).unwrap();
    let cert_error = crate::with_decode_resource_limits(
        crate::DecodeResourceLimits {
            max_nodes: 1_000,
            max_depth: 32,
        },
        || {
            bincode::serde::decode_from_slice::<ProofCert, _>(
                &cert_bytes,
                bincode::config::standard(),
            )
        },
    )
    .expect_err("deep certificate must fail inside the scoped decoder");
    assert!(cert_error.to_string().contains("structural depth"));

    let step = deep_step(128);
    let step_json = serde_json::to_vec(&step).unwrap();
    let step_json_error = crate::with_decode_resource_limits(
        crate::DecodeResourceLimits {
            max_nodes: 1_000,
            max_depth: 32,
        },
        || serde_json::from_slice::<DefEqStep>(&step_json),
    )
    .expect_err("deep JSON definitional-equality trace must fail inside the scoped decoder");
    assert!(step_json_error.to_string().contains("structural depth"));

    let step_bytes = bincode::serde::encode_to_vec(&step, bincode::config::standard()).unwrap();
    let step_error = crate::with_decode_resource_limits(
        crate::DecodeResourceLimits {
            max_nodes: 1_000,
            max_depth: 32,
        },
        || {
            bincode::serde::decode_from_slice::<DefEqStep, _>(
                &step_bytes,
                bincode::config::standard(),
            )
        },
    )
    .expect_err("deep definitional-equality trace must fail inside the scoped decoder");
    assert!(step_error.to_string().contains("structural depth"));
}

#[test]
fn certificate_decode_node_limits_fail_closed() {
    let cert = ProofCert::App {
        fn_cert: leaf(),
        fn_type: Box::new(Expr::prop()),
        arg_cert: leaf(),
        result_type: Box::new(Expr::prop()),
    };
    let cert_bytes = bincode::serde::encode_to_vec(cert, bincode::config::standard()).unwrap();
    let cert_error = crate::with_decode_resource_limits(
        crate::DecodeResourceLimits {
            max_nodes: 1,
            max_depth: 100,
        },
        || {
            bincode::serde::decode_from_slice::<ProofCert, _>(
                &cert_bytes,
                bincode::config::standard(),
            )
        },
    )
    .expect_err("certificate child must exceed the one-node budget");
    assert!(cert_error.to_string().contains("structural node count"));

    let step = DefEqStep::Struct("node-budget".to_owned(), vec![DefEqStep::Refl]);
    let step_bytes = bincode::serde::encode_to_vec(step, bincode::config::standard()).unwrap();
    let step_error = crate::with_decode_resource_limits(
        crate::DecodeResourceLimits {
            max_nodes: 1,
            max_depth: 100,
        },
        || {
            bincode::serde::decode_from_slice::<DefEqStep, _>(
                &step_bytes,
                bincode::config::standard(),
            )
        },
    )
    .expect_err("trace child must exceed the one-node budget");
    assert!(step_error.to_string().contains("structural node count"));
}

// ========================================================================
// Proof Replay tests
// ========================================================================
