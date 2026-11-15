// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression pin — WS6.10 (F-107): `UIntA.toUIntB` width conversions.
//!
//! ## The gap (proof program, `GENERAL.p12b_width_conversion.widen.emit`)
//!
//! ```text
//! def widen (a : UInt8) : UInt64 := UInt8.toUInt64 a   -- Unknown identifier
//! ```
//!
//! The kernel named native reducers for all twelve fixed-width conversions
//! (`native_reducers_uint_conv.rs`) but the with-prelude overlay defined no
//! constant for any of them. `init_one_uint_arith` now defines each as
//! `<target>.ofNat (<source>.toNat x)`: narrowing wraps mod `2^target`,
//! widening is exact. The values below are decided by the KERNEL (`rfl`
//! theorems kernel-checked, plus `is_def_eq`), not reported by the elaborator.

use clean_elab::{
    elaborate_decl_and_register, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, TypeChecker};
use clean_parser::parse_file;

/// Drive the real file pipeline, kernel-checking every definition and theorem
/// it produces against its declared type before registering it.
fn elaborate_file(source: &str) -> Result<(Environment, Vec<(String, Expr)>), String> {
    let mut env = Environment::with_prelude();
    let mut file_ctx = FileContext::new();
    let decls = parse_file(source).map_err(|e| format!("parse error: {e:?}"))?;
    let mut values = Vec::new();
    for decl in &decls {
        let processed = preprocess_decl_with_context(decl, &mut file_ctx);
        let result =
            elaborate_decl_and_register(&mut env, &processed).map_err(|e| e.to_string())?;
        match &result {
            ElabResult::Definition { name, ty, val, .. } => {
                let tc = TypeChecker::new(&env);
                tc.check_type(val, ty)
                    .map_err(|e| format!("kernel rejected {name}: {e}"))?;
                values.push((name.to_string(), val.clone()));
            }
            ElabResult::Theorem {
                name, ty, proof, ..
            } => {
                let tc = TypeChecker::new(&env);
                tc.check_type(proof, ty)
                    .map_err(|e| format!("kernel rejected {name}: {e}"))?;
            }
            _ => {}
        }
    }
    Ok((env, values))
}

fn expect_accepted(source: &str) -> (Environment, Vec<(String, Expr)>) {
    elaborate_file(source)
        .unwrap_or_else(|e| panic!("must elaborate and kernel-check, got: {e}\n{source}"))
}

fn expect_refusal(source: &str) -> String {
    match elaborate_file(source) {
        Ok(_) => panic!("must be REFUSED, but elaborated:\n{source}"),
        Err(e) => e,
    }
}

/// The p12b probe itself, verbatim, plus its expected-value vectors
/// (`should_emit/p12b_width_conversion.expected.json`: 0, 200, 255) as `rfl`
/// theorems.
const P12B: &str = "def widen (a : UInt8) : UInt64 := UInt8.toUInt64 a\n";

/// Positive (the increment's named fixture): `widen` elaborates in dot form,
/// and `widen 255 = 255` is proved by `rfl`.
#[test]
fn ws6_10_widen_elaborates_and_widen_255_is_rfl() {
    let _ = expect_accepted(
        "def widen (a : UInt8) : UInt64 := a.toUInt64\n\n\
         theorem widen_255 : widen 255 = 255 := rfl\n",
    );
}

/// Port of the proof-program row `GENERAL.p12b_width_conversion.widen.emit`,
/// front-end half: the probe source was refused before lowering
/// (PRODUCER-GAP, "toUInt64" unknown). It now elaborates and computes the
/// zero-extension model at every expected vector.
#[test]
fn general_p12b_width_conversion_widen_elaborates() {
    let source = format!(
        "{P12B}\n\
         theorem t_widen_0 : widen 0 = 0 := rfl\n\n\
         theorem t_widen_1 : widen 200 = 200 := rfl\n\n\
         theorem t_widen_2 : widen 255 = 255 := rfl\n"
    );
    let _ = expect_accepted(&source);
}

/// Negative twin (REVIEW-corrected values): narrowing WRAPS, `300 - 256 = 44`.
/// `= 44` proves; `= 45` is refused, and refused BY THE KERNEL's
/// definitional-equality check on the `rfl` (the source differs from the
/// proving one by the single digit).
#[test]
fn ws6_10_narrowing_wraps_300_to_44_and_not_45() {
    let _ = expect_accepted("theorem narrow : (300 : UInt16).toUInt8 = 44 := rfl\n");
    let err = expect_refusal("theorem narrow : (300 : UInt16).toUInt8 = 45 := rfl\n");
    assert!(
        err.contains("Type mismatch") && err.contains("= UInt8.ofNat 45"),
        "the refusal must be the kernel's definitional-equality failure on the \
         `rfl`, naming the false right-hand side, got: {err}"
    );
    assert!(
        !err.to_lowercase().contains("unknown identifier"),
        "the refusal must not be the pre-WS6.10 missing-constant one, got: {err}"
    );
}

/// Every one of the twelve fixed-width conversions elaborates in dot form and
/// computes Lean 4's value: truncation when narrowing, identity when widening.
/// One file, one environment: each conversion gets a `lhs_i`, its true value
/// `ok_i` and a one-off `bad_i`, and the KERNEL must equate the first pair and
/// separate the second — so the check discriminates rather than accepting any
/// value.
#[test]
fn ws6_10_all_twelve_conversions_compute_lean_values() {
    let cases: [(&str, &str, u64, u64); 12] = [
        ("UInt16", "UInt8", 300, 44),
        ("UInt32", "UInt8", 1_000, 232),
        ("UInt32", "UInt16", 70_000, 4_464),
        ("UInt64", "UInt8", 257, 1),
        ("UInt64", "UInt16", 65_537, 1),
        ("UInt64", "UInt32", 4_294_967_297, 1),
        ("UInt8", "UInt16", 255, 255),
        ("UInt8", "UInt32", 200, 200),
        ("UInt8", "UInt64", 128, 128),
        ("UInt16", "UInt32", 65_535, 65_535),
        ("UInt16", "UInt64", 60_000, 60_000),
        ("UInt32", "UInt64", 4_294_967_295, 4_294_967_295),
    ];
    let mut src = String::new();
    for (i, (source, target, input, expected)) in cases.iter().enumerate() {
        src.push_str(&format!(
            "def lhs_{i} : {target} := ({input} : {source}).to{target}\n\n\
             def ok_{i} : {target} := {expected}\n\n\
             def bad_{i} : {target} := {}\n\n",
            expected + 1
        ));
    }
    let (env, values) = expect_accepted(&src);
    let value = |name: &str| {
        &values
            .iter()
            .find(|(n, _)| n == name)
            .unwrap_or_else(|| panic!("no definition {name}"))
            .1
    };
    let tc = TypeChecker::with_mode(&env, env.mode());
    for (i, (source, target, input, expected)) in cases.iter().enumerate() {
        let lhs = value(&format!("lhs_{i}"));
        assert!(
            tc.is_def_eq(lhs, value(&format!("ok_{i}"))),
            "{source}.to{target} {input} must reduce to {expected}"
        );
        assert!(
            !tc.is_def_eq(lhs, value(&format!("bad_{i}"))),
            "{source}.to{target} {input} must NOT reduce to {}",
            expected + 1
        );
    }
}

/// `USize` conversions stay undefined in the native prelude: its width is
/// platform-abstract, so a portable definition would claim what the prelude
/// cannot ground. The refusal names the missing constant.
#[test]
fn ws6_10_usize_conversion_stays_refused() {
    let err = expect_refusal("def w (a : UInt8) : USize := a.toUSize\n");
    assert!(
        err.contains("toUSize"),
        "the USize conversion must be refused naming the missing constant, got: {err}"
    );
}

/// WS6.10 review (adversarial): conversions COMPOSE with the kernel's value
/// semantics — narrow-then-widen truncates exactly once — and widening never
/// invents a carry: `(255 : UInt8).toUInt64 = 256` is refused by the kernel's
/// def-eq, not accepted by a reducer that forgot the source width.
#[test]
fn ws6_10_review_composed_conversions_truncate_once_and_widening_is_exact() {
    let _ = expect_accepted(
        "theorem w : (65535 : UInt16).toUInt8.toUInt64 = 255 := rfl\n\n\
         theorem x : (4294967296 : UInt64).toUInt32.toUInt64 = 0 := rfl\n",
    );
    let err = expect_refusal("theorem w2 : (255 : UInt8).toUInt64 = 256 := rfl\n");
    assert!(
        err.contains("Type mismatch") && err.contains("UInt64.ofNat 256"),
        "the refusal must be the kernel's def-eq failure naming the false value, got: {err}"
    );
}
