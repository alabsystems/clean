// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Env-gated forensic probe for snapshot decode failures: decodes
//! progressively longer FIELD PREFIXES of a real snapshot payload (bincode is
//! positional, so a tuple mirrors a struct prefix) to pinpoint which field's
//! serde graph fails. Inert without `ISA_SNAPPROBE=<snapshot-path>`.

use std::collections::BTreeMap;
use std::io::Read as _;

use clean_kernel::Environment;
use clean_mathverse::hol::isabelle_pure_verify::PureVerifiedImport;

/// The first snapshot format whose header carries the 32-byte ENV-LAYOUT
/// fingerprint between the version and the payload length (mirrors
/// `snapshot::LAYOUT_FP_MIN_VERSION`).
const LAYOUT_FP_MIN_VERSION: u32 = 6;

fn read_payload(path: &str) -> Vec<u8> {
    let mut f = std::fs::File::open(path).expect("open snapshot");
    let mut magic = [0u8; 8];
    f.read_exact(&mut magic).expect("magic");
    let mut ver = [0u8; 4];
    f.read_exact(&mut ver).expect("version");
    let version = u32::from_le_bytes(ver);
    println!("format version: {version}");
    // v6+ ENV-LAYOUT guard: skip the 32-byte fingerprint that now precedes the
    // payload length (see `snapshot::env_layout_fingerprint`).
    if version >= LAYOUT_FP_MIN_VERSION {
        let mut layout_fp = [0u8; 32];
        f.read_exact(&mut layout_fp)
            .expect("env-layout fingerprint");
    }
    let mut len8 = [0u8; 8];
    f.read_exact(&mut len8).expect("len");
    let len = usize::try_from(u64::from_le_bytes(len8)).expect("len fits");
    let mut payload = vec![0u8; len];
    f.read_exact(&mut payload).expect("payload");
    payload
}

fn probe<T: serde::de::DeserializeOwned>(payload: &[u8], label: &str) -> bool {
    match bincode::serde::decode_from_slice::<T, _>(payload, bincode::config::standard()) {
        Ok((_, used)) => {
            println!("OK   {label} (consumed {used} bytes)");
            true
        }
        Err(e) => {
            println!("FAIL {label}: {e}");
            false
        }
    }
}

#[test]
fn snapshot_probe_if_env_set() {
    let Ok(path) = std::env::var("ISA_SNAPPROBE") else {
        return;
    };
    let payload = read_payload(&path);
    println!("payload: {} bytes", payload.len());

    probe::<(String,)>(&payload, "fingerprint");
    probe::<(String, usize)>(&payload, "+prefix_lines");
    probe::<(String, usize, u64)>(&payload, "+prefix_bytes");
    probe::<(String, usize, u64, [u8; 32])>(&payload, "+prefix_blake3");
    probe::<(String, usize, u64, [u8; 32], PureVerifiedImport)>(&payload, "+out");
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
    )>(&payload, "+env");
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
        BTreeMap<i64, clean_mathverse::hol::isabelle_pure_translate::ClosureEntry>,
    )>(&payload, "+closure");
    use clean_mathverse::hol::isabelle_pure_translate::{
        ClassRegistry, InstanceOpRegistry, ListFnRegistry, MethodRegistry, PolyInstRegistry,
    };
    type Closure = BTreeMap<i64, clean_mathverse::hol::isabelle_pure_translate::ClosureEntry>;
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
        Closure,
        ClassRegistry,
    )>(&payload, "+class_registry");
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
        Closure,
        ClassRegistry,
        MethodRegistry,
    )>(&payload, "+method_registry");
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
        Closure,
        ClassRegistry,
        MethodRegistry,
        InstanceOpRegistry,
    )>(&payload, "+instance_op_registry");
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
        Closure,
        ClassRegistry,
        MethodRegistry,
        InstanceOpRegistry,
        ListFnRegistry,
    )>(&payload, "+list_fn_registry");
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
        Closure,
        ClassRegistry,
        MethodRegistry,
        InstanceOpRegistry,
        ListFnRegistry,
        PolyInstRegistry,
    )>(&payload, "+poly_inst_registry");
    probe::<(
        String,
        usize,
        u64,
        [u8; 32],
        PureVerifiedImport,
        Environment,
        Closure,
        ClassRegistry,
        MethodRegistry,
        InstanceOpRegistry,
        ListFnRegistry,
        PolyInstRegistry,
        BTreeMap<String, usize>,
    )>(&payload, "+rejection_reasons (FULL v2 layout)");
}
