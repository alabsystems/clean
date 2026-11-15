// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Parsed BVar Nat validity and exact represented indices, not kernel admission.
use super::*;
use crate::import::{convert_expr, read_and_convert_expr, ExprInternCache};

const BASE: u64 = 0x10000;

struct Raw(Vec<u8>);
impl Raw {
    fn new() -> Self {
        let mut bytes = vec![0; 152];
        bytes[..5].copy_from_slice(b"olean");
        bytes[5] = 2;
        bytes[6] = 1;
        bytes[7..17].copy_from_slice(b"4.30.0-rc2");
        bytes[40..80].fill(b'a');
        bytes[80..88].copy_from_slice(&BASE.to_le_bytes());
        bytes[88..96].copy_from_slice(&(BASE + 96).to_le_bytes());
        bytes[100..102].copy_from_slice(&56u16.to_le_bytes());
        bytes[102] = 5;
        for index in 0..5 {
            bytes[104 + index * 8..112 + index * 8].copy_from_slice(&1u64.to_le_bytes());
        }
        Self(bytes)
    }
    fn bvar(&mut self, index: u64) -> usize {
        let offset = self.0.len();
        self.0.extend_from_slice(&[0, 0, 0, 0, 24, 0, 1, 0]);
        self.0.extend_from_slice(&index.to_le_bytes());
        self.0.extend_from_slice(&[0; 8]);
        offset
    }
    fn mpz(&mut self, limbs: &[u64]) -> u64 {
        let ptr = BASE + self.0.len() as u64;
        self.0.extend_from_slice(&[0; 4]);
        self.0
            .extend_from_slice(&((24 + limbs.len() * 8) as u16).to_le_bytes());
        self.0.extend_from_slice(&[0, tags::MPZ]);
        self.0
            .extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.0
            .extend_from_slice(&(limbs.len() as i32).to_le_bytes());
        self.0.extend_from_slice(&(ptr + 24).to_le_bytes());
        for limb in limbs {
            self.0.extend_from_slice(&limb.to_le_bytes());
        }
        ptr
    }
    fn read(&self, offset: usize) -> OleanResult<ParsedExpr> {
        CompactedRegion::new(&self.0, BASE).read_expr_at(offset)
    }
}

#[test]
fn null_bvar_nat_refuses_instead_of_inventing_zero() {
    let mut raw = Raw::new();
    let offset = raw.bvar(0);
    assert!(raw.read(offset).is_err());
    raw.0[..64].fill(0);
    raw.0[offset + 4] = 0;
    raw.0[offset + 6] = 0;
    assert!(
        raw.read(offset).is_err(),
        "legacy scratch null is not tagged zero"
    );
}

#[test]
fn legacy_and_modern_small_bvar_indices_remain_exact() {
    for index in [0u64, 4, clean_kernel::Expr::MAX_BVAR_INDEX.into()] {
        let mut raw = Raw::new();
        let offset = raw.bvar((index << 1) | 1);
        assert_eq!(raw.read(offset).unwrap(), ParsedExpr::BVar(index));
        raw.0[..64].fill(0);
        raw.0[offset + 4] = 0;
        raw.0[offset + 6] = 0;
        assert_eq!(raw.read(offset).unwrap(), ParsedExpr::BVar(index));
    }
}

#[test]
fn boxed_u64_bvars_preserve_parsed_value_but_exceed_kernel_carrier() {
    for index in [1u64 << 63, u64::MAX] {
        let mut raw = Raw::new();
        let heap = raw.mpz(&[index]);
        let offset = raw.bvar(heap);
        let parsed = raw.read(offset).unwrap();
        assert_eq!(parsed, ParsedExpr::BVar(index));
        assert!(convert_expr("boxed-bvar", &parsed, &mut ExprInternCache::default()).is_err());
        let region = CompactedRegion::new(&raw.0, BASE);
        assert!(read_and_convert_expr(
            &region,
            region.offset_to_ptr(offset),
            "boxed-bvar",
            &mut ExprInternCache::default()
        )
        .is_err());
    }
}

#[test]
fn over_u64_bvar_index_never_truncates_to_zero() {
    let mut raw = Raw::new();
    let heap = raw.mpz(&[0, 1]);
    let offset = raw.bvar(heap);
    assert!(raw.read(offset).is_err());
}

#[test]
fn malformed_boxed_bvar_nats_refuse() {
    for (relative, value) in [
        (0, 1),
        (4, 24),
        (6, 1),
        (7, 249),
        (8, 2),
        (12, 0),
        (15, 255),
        (16, 0),
        (31, 0),
    ] {
        let mut raw = Raw::new();
        let heap = raw.mpz(&[1u64 << 63]);
        let offset = raw.bvar(heap);
        raw.0[(heap - BASE) as usize + relative] = value;
        assert!(raw.read(offset).is_err(), "MPZ mutation at {relative}");
    }
    let mut raw = Raw::new();
    let heap = raw.mpz(&[1u64 << 63]);
    let offset = raw.bvar(heap);
    raw.0[6] = 0;
    assert!(
        raw.read(offset).is_err(),
        "unmeasured non-GMP heap encoding"
    );
}

#[test]
fn missing_and_outside_bvar_nat_payloads_refuse() {
    for ptr in [BASE - 8, BASE + 0x100000] {
        let mut raw = Raw::new();
        let offset = raw.bvar(ptr);
        assert!(raw.read(offset).is_err());
    }
    let mut raw = Raw::new();
    let offset = raw.bvar(1);
    raw.0.truncate(offset + 12);
    assert!(raw.read(offset).is_err());
}

fn bvars(expr: &ParsedExpr, output: &mut Vec<u64>) {
    match expr {
        ParsedExpr::BVar(index) => output.push(*index),
        ParsedExpr::App(f, a) => {
            bvars(f, output);
            bvars(a, output);
        }
        ParsedExpr::Lam(_, t, b, _) | ParsedExpr::ForallE(_, t, b, _) => {
            bvars(t, output);
            bvars(b, output);
        }
        ParsedExpr::LetE(_, t, v, b, _) => {
            bvars(t, output);
            bvars(v, output);
            bvars(b, output);
        }
        ParsedExpr::MData(_, v) | ParsedExpr::Proj(_, _, v) => bvars(v, output),
        _ => {}
    }
}
fn oracle_bvars(value: &serde_json::Value, output: &mut Vec<u64>) {
    if value["tag"] == "bvar" {
        output.push(value["index"].as_u64().unwrap());
        return;
    }
    match value {
        serde_json::Value::Array(items) => {
            for item in items {
                oracle_bvars(item, output);
            }
        }
        serde_json::Value::Object(fields) => {
            for item in fields.values() {
                oracle_bvars(item, output);
            }
        }
        _ => {}
    }
}

/// The `runtime_probe` family (`tests/fixtures/lean/v4.30.0-rc2/runtime_probe/
/// README.md`) compiled by the pinned Lean on first use, read against the
/// independent upstream oracle (`oracle/DumpOlean.lean`, run by the same binary
/// over the whole triple so the document is the one `tests/runtime_declarations.rs`
/// reads). Only the base part's rows are compared here, so the row count is the
/// oracle's `parts[0].constants.len()` (measured 24 on 2026-09-15), never a
/// literal. Fails closed when the toolchain is absent.
#[test]
fn actual_source_bvar_occurrences_match_all_base_rows() {
    let root = crate::test_support::compiled_fixture_dir("runtime_probe");
    let paths =
        ["", ".server", ".private"].map(|suffix| root.join(format!("RuntimeProbe.olean{suffix}")));
    let data = std::fs::read(&paths[0]).unwrap();
    let args = paths
        .each_ref()
        .map(|path| path.to_str().expect("utf-8 fixture path"));
    let oracle = crate::test_support::run_oracle(&args);
    let header = crate::header::OleanHeader::parse(&data).unwrap();
    let region = CompactedRegion::new(&data, header.base_addr);
    let module = region.read_module_data_opts(false).unwrap();
    let expected = oracle["parts"][0]["constants"].as_array().unwrap();
    assert!(!expected.is_empty());
    assert_eq!(module.constants.len(), expected.len());
    let mut total = 0;
    for (row, source) in module.constants.iter().zip(expected) {
        for (parsed, core) in [
            (&row.type_, &source["type_core"]),
            (&row.value, &source["value_core"]),
        ] {
            assert_eq!(parsed.is_some(), !core.is_null());
            let mut actual = Vec::new();
            let mut expected = Vec::new();
            if let Some(expr) = parsed {
                bvars(expr, &mut actual);
            }
            oracle_bvars(core, &mut expected);
            actual.sort();
            expected.sort();
            assert_eq!(
                actual, expected,
                "BVar type/value occurrence mismatch for {}",
                row.name
            );
            total += actual.len();
        }
    }
    assert!(total > 0);
    println!(
        "all {} base type/value rows retained; exact BVar occurrences={total}",
        expected.len()
    );
}

/// Needs only the pinned toolchain's `lib/lean/Init/Prelude.olean`; fails
/// closed when that toolchain is absent. Measured 2026-09-15 (`cargo +trust
/// test --locked -p clean-olean --lib
/// expr::bvar_tests::exact_prelude_candidate_parity_reports_both_decoders`):
/// 200 candidates, `mismatches == 0`, 0.02 s.
#[test]
fn exact_prelude_candidate_parity_reports_both_decoders() {
    // Until 2026-09-15 this read `CLEAN_OLEAN_PINNED_LEAN_LIB` with `std::env::var`
    // at RUNTIME, where cargo never sets it (build.rs emits it as a compile-time
    // `cargo:rustc-env` only), so the test could not run without a hand-exported
    // shell variable. `pinned_lean_lib_path()` honours the compile-time value and
    // falls back to the workspace `lean-toolchain` pin; the `expect` is the
    // owner's fail-closed spelling (`companion_root_tests`).
    let lib = crate::pinned_lean_lib_path().expect("explicit pinned Lean fixture is required");
    let data = std::fs::read(lib.join("Init/Prelude.olean")).unwrap();
    let header = crate::header::OleanHeader::parse(&data).unwrap();
    let region = CompactedRegion::new(&data, header.base_addr);
    let candidates = region.find_expr_objects();
    assert!(candidates.len() >= 200);
    let mut mismatches = 0;
    for (offset, _, _) in candidates.iter().take(200) {
        let parsed = region.read_expr_at(*offset);
        let two_phase = parsed.as_ref().map_err(|e| e.to_string()).and_then(|e| {
            convert_expr("test", e, &mut ExprInternCache::default())
                .map(|(e, _)| e)
                .map_err(|e| e.to_string())
        });
        let direct = read_and_convert_expr(
            &region,
            region.offset_to_ptr(*offset),
            "test",
            &mut ExprInternCache::default(),
        )
        .map(|(e, _)| e)
        .map_err(|e| e.to_string());
        if two_phase.as_ref().ok() != direct.as_ref().ok() {
            mismatches += 1;
            println!("candidate offset={offset} header={:?} bytes={:02x?} parsed={parsed:?} two_phase={two_phase:?} direct={direct:?}", region.read_header_at(*offset), &data[*offset..(*offset + 48).min(data.len())]);
        }
    }
    assert_eq!(mismatches, 0);
}
