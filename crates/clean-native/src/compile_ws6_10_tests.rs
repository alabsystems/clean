// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.10 (F-107) through the exact `clean compile` lowering: fixed-width
//! `UIntA.toUIntB` conversions reach the trust-ir emitter as ONE native
//! `zext`/`trunc`. A child of `battery_census_tests`, so the
//! `trust-ir-backend-lib` gate leg (`-- compile::battery_census_tests::`)
//! runs it.

use super::*;

/// WS6.10 (F-107): port of the proof-program row
/// `GENERAL.p12b_width_conversion.widen.emit` (was PRODUCER-GAP). The p12b
/// probe sits outside the 20-root census battery above: at the recorded tree
/// `clean compile` refused it before lowering, because `UInt8.toUInt64` was
/// not a prelude constant. The probe now emits `--emit trustir` text AND the
/// linkable `--emit trustir-bin` artifact, and the artifact decodes with
/// `widen` DEFINED as ONE native `zext u8 → u64` — the conversion is on the
/// emitter's native table, so its compiled-from-source body is skipped and no
/// call to it remains.
///
/// Negative twin: a `USize` conversion, which the native prelude deliberately
/// does not define (its width is platform-abstract), is still refused before
/// lowering, naming the missing constant.
#[test]
fn general_p12b_width_conversion_widen_emit() {
    const P12B: &str = "def widen (a : UInt8) : UInt64 := UInt8.toUInt64 a\n";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("p12b_width_conversion.lean");
    std::fs::write(&file, P12B).expect("write probe");
    let args = |emit, output| CompileArgs {
        file: Some(file.clone()),
        decl: Some("widen".to_owned()),
        emit,
        opt_level: 0,
        output,
        link_artifact: Vec::new(),
    };

    let text = super::super::compile_to_string(args(EmitFormat::Trustir, None))
        .unwrap_or_else(|e| panic!("p12b must emit trust-ir text: {e:#}"));
    assert!(
        text.contains("fn @widen("),
        "`widen` must be emitted:\n{text}"
    );
    assert!(
        text.contains("zext u8 %0 to u64"),
        "`widen` must lower to a native zext:\n{text}"
    );

    let out = dir.path().join("widen.bin");
    super::super::compile_to_trustir_bin(&args(EmitFormat::TrustirBin, Some(out.clone())))
        .unwrap_or_else(|e| panic!("p12b must emit the linkable artifact: {e:#}"));
    let module = deserialize_module_bytes(&std::fs::read(&out).expect("artifact"))
        .expect("the canonical reader must accept the artifact");
    let widen = module
        .functions
        .iter()
        .find(|f| f.name == "widen" && !f.blocks.is_empty())
        .expect("`widen` must be DEFINED in the emitted module");
    // clean-native has no direct `trust-ir` dependency: read the instructions
    // through their `Debug` spelling.
    let insts: Vec<String> = widen
        .instructions()
        .map(|n| format!("{:?}", n.inst))
        .collect();
    assert!(
        insts.len() == 2
            && insts[0].starts_with("Cast { op: ZExt, src_ty: U8, dst_ty: U64,")
            && insts[1].starts_with("Return"),
        "`widen` must be exactly `zext u8 -> u64; ret`, got: {insts:?}"
    );
    assert!(
        module.functions.iter().all(|f| f.name != "UInt8.toUInt64"),
        "the conversion is native: its compiled body must not be emitted"
    );

    let twin = dir.path().join("usize_twin.lean");
    std::fs::write(&twin, "def w (a : UInt8) : USize := UInt8.toUSize a\n").expect("write twin");
    let err = super::super::compile_to_string(CompileArgs {
        file: Some(twin),
        decl: Some("w".to_owned()),
        emit: EmitFormat::Trustir,
        opt_level: 0,
        output: None,
        link_artifact: Vec::new(),
    })
    .expect_err("a USize conversion must still be refused");
    assert!(
        format!("{err:#}").contains("toUSize"),
        "the refusal must name the missing conversion: {err:#}"
    );
}

/// WS6.10 review (adversarial, REAL pipeline): the emitter tests drive the
/// conversion arm over hand-built IR; these drive it through the full
/// `clean compile` pipeline on shapes the implementation was not written
/// against, and read back the validated linkable artifact:
///
/// - `chain`: a narrowing CHAIN is exactly two truncations, in order
///   (`trunc u64→u32; trunc u32→u8; ret`), never one `u64→u8` truncation of a
///   value the middle conversion should have wrapped first (same result, but a
///   reordered or fused cast is a different program than the source says);
/// - `proj`: an operand projected out of a boxed `Option` is unboxed to `u8`
///   BEFORE the `zext`, so the cast arm's operand-type check accepts it (a
///   legitimate module is not refused);
/// - `mapped`: `UInt8.toUInt64` passed as a function VALUE to `List.map`
///   compiles, and no bodyless `UInt8.toUInt64` declaration is left behind as
///   an unresolvable link-time symbol.
#[test]
fn ws6_10_review_width_conversions_through_the_real_pipeline() {
    const SRC: &str = "\
def chain (x : UInt64) : UInt8 := (x.toUInt32).toUInt8

def proj (o : Option UInt8) : UInt64 := match o with
  | some a => a.toUInt64
  | none => 0

def mapped (xs : List UInt8) : List UInt64 := xs.map UInt8.toUInt64
";
    let dir = tempfile::tempdir().expect("tempdir");
    let file = dir.path().join("ws6_10_review.lean");
    std::fs::write(&file, SRC).expect("write probe");
    // `(name, defined, instructions in Debug spelling)` per function — clean-native
    // has no direct `trust-ir` dependency, so the module type is not nameable.
    let emit = |decl: &str| -> Vec<(String, bool, Vec<String>)> {
        let out = dir.path().join(format!("{decl}.bin"));
        super::super::compile_to_trustir_bin(&CompileArgs {
            file: Some(file.clone()),
            decl: Some(decl.to_owned()),
            emit: EmitFormat::TrustirBin,
            opt_level: 0,
            output: Some(out.clone()),
            link_artifact: Vec::new(),
        })
        .unwrap_or_else(|e| panic!("`{decl}` must emit a validated artifact: {e:#}"));
        let module = deserialize_module_bytes(&std::fs::read(&out).expect("artifact"))
            .expect("the canonical reader must accept the artifact");
        module
            .functions
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    !f.blocks.is_empty(),
                    f.instructions().map(|n| format!("{:?}", n.inst)).collect(),
                )
            })
            .collect()
    };
    let insts_of = |fns: &[(String, bool, Vec<String>)], name: &str| -> Vec<String> {
        fns.iter()
            .find(|(n, defined, _)| n == name && *defined)
            .unwrap_or_else(|| panic!("`{name}` must be DEFINED"))
            .2
            .clone()
    };
    let no_conversion_symbol = |fns: &[(String, bool, Vec<String>)]| {
        assert!(
            fns.iter()
                .all(|(n, defined, _)| *defined || !n.contains("toUInt")),
            "no width conversion may be left as a bodyless external: {:?}",
            fns.iter().map(|f| (&f.0, f.1)).collect::<Vec<_>>()
        );
    };

    let chain = emit("chain");
    let insts = insts_of(&chain, "chain");
    assert!(
        insts.len() == 3
            && insts[0].starts_with("Cast { op: Trunc, src_ty: U64, dst_ty: U32,")
            && insts[1].starts_with("Cast { op: Trunc, src_ty: U32, dst_ty: U8,")
            && insts[2].starts_with("Return"),
        "`chain` must be exactly `trunc u64->u32; trunc u32->u8; ret`, got: {insts:?}"
    );
    no_conversion_symbol(&chain);

    let proj = emit("proj");
    let insts = insts_of(&proj, "proj");
    assert!(
        insts
            .iter()
            .any(|i| i.starts_with("Cast { op: ZExt, src_ty: U8, dst_ty: U64,")),
        "`proj` must widen the unboxed u8 with one zext, got: {insts:?}"
    );
    no_conversion_symbol(&proj);

    let mapped = emit("mapped");
    no_conversion_symbol(&mapped);
}
