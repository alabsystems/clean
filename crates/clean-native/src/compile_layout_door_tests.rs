// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Rule C1 (the runtime header's widths, `clean-compiler`'s
//! `ir_checker/layout.rs`) at every trust-ir door of `clean compile`.
//!
//! `--emit trustir`, `--emit trustir-bin` and `--emit obj` all lower through
//! `compile_lcnf_to_trust_ir`, which emitted without the L5IR checker: a
//! constructor the C lane refuses by name compiled silently there and was
//! caught, if at all, by a runtime panic. The pipeline now checks the boxed
//! declarations before it emits trust-ir, so each door refuses by name at build
//! time. A child of `battery_census_tests`, so the `trust-ir-backend-lib` gate
//! leg (`-- compile::battery_census_tests::`) runs it.

use super::*;

/// `structure W` of `n` `UInt64` fields and `mk` building it: `8 * n` bytes of
/// scalar area. 32 fields are 256 bytes, which the header's 8-bit `scalar_sz`
/// truncates to 0; 31 fields (248 bytes) fit.
fn wide_scalars(n: usize) -> String {
    let fields: String = (0..n).map(|i| format!("  f{i} : UInt64\n")).collect();
    let inits: Vec<String> = (0..n).map(|i| format!("f{i} := n")).collect();
    format!(
        "structure W where\n{fields}\ndef mk (n : UInt64) : W := {{ {} }}\n",
        inits.join(", ")
    )
}

/// `inductive Big` of `last` nullary constructors and then `c{last} (n : Nat)`,
/// whose field makes it a heap constructor carrying tag `last`, and `mk`
/// building it. Pinned Lean refuses tag 244 ("tag for constructor 'Big.c244'
/// is too big", `LeanMaxCtorTag`) and runs tag 243.
fn heap_ctor_tag(last: u32) -> String {
    let nullary: String = (0..last).map(|i| format!("  | c{i}\n")).collect();
    format!(
        "inductive Big where\n{nullary}  | c{last} (n : Nat)\n\n\
         def mk (n : Nat) : Big := Big.c{last} n\n"
    )
}

fn args(file: &Path, emit: EmitFormat, output: Option<PathBuf>) -> CompileArgs {
    CompileArgs {
        file: Some(file.to_path_buf()),
        decl: Some("mk".to_owned()),
        emit,
        opt_level: 0,
        output,
        link_artifact: Vec::new(),
    }
}

fn write(dir: &Path, stem: &str, source: &str) -> PathBuf {
    let file = dir.join(format!("{stem}.lean"));
    std::fs::write(&file, source).expect("write probe");
    file
}

/// A 256-byte scalar area is refused by name at all three trust-ir doors, and
/// none of them writes its output; the 248-byte control still emits.
#[test]
fn trust_ir_doors_refuse_a_256_byte_scalar_area_by_name() {
    const REFUSAL: &str = "constructor W.mk has 256 bytes of scalar fields";
    let dir = tempfile::tempdir().expect("tempdir");
    let wide = write(dir.path(), "wide32", &wide_scalars(32));

    let err = super::super::compile_to_string(args(&wide, EmitFormat::Trustir, None))
        .expect_err("--emit trustir must refuse a 256-byte scalar area");
    assert!(
        format!("{err:#}").contains(REFUSAL),
        "--emit trustir must refuse by name: {err:#}"
    );

    let bin = dir.path().join("wide32.bin");
    let err = super::super::compile_to_trustir_bin(&args(
        &wide,
        EmitFormat::TrustirBin,
        Some(bin.clone()),
    ))
    .expect_err("--emit trustir-bin must refuse a 256-byte scalar area");
    assert!(
        format!("{err:#}").contains(REFUSAL),
        "--emit trustir-bin must refuse by name: {err:#}"
    );
    assert!(
        !bin.exists(),
        "a refused trustir-bin must write no artifact"
    );

    // `--emit obj` locates trust-cg before it lowers; with none on this box it
    // is refused for that, by name, and the two doors above carry the claim.
    let obj = dir.path().join("wide32.o");
    let err = super::super::compile_to_object(&args(&wide, EmitFormat::Obj, Some(obj.clone())))
        .expect_err("--emit obj must refuse a 256-byte scalar area");
    let expected = if find_trust_cg().expect("valid trust-cg selection").is_some() {
        REFUSAL
    } else {
        "trust-cg binary not found"
    };
    assert!(
        format!("{err:#}").contains(expected),
        "--emit obj must refuse with {expected:?}: {err:#}"
    );
    assert!(!obj.exists(), "a refused --emit obj must write no object");

    let fits = write(dir.path(), "wide31", &wide_scalars(31));
    let text = super::super::compile_to_string(args(&fits, EmitFormat::Trustir, None))
        .unwrap_or_else(|e| panic!("248 scalar bytes fit the header and must emit: {e:#}"));
    assert!(text.contains("@mk("), "`mk` must be emitted:\n{text}");
}

/// The Lean-parity refusal (R2): a heap constructor tag above `LeanMaxCtorTag`
/// is refused at `--emit trustir` as pinned Lean refuses it.
#[test]
fn trust_ir_door_refuses_heap_ctor_tag_244_by_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    let big = write(dir.path(), "tag244", &heap_ctor_tag(244));
    let err = super::super::compile_to_string(args(&big, EmitFormat::Trustir, None))
        .expect_err("--emit trustir must refuse heap constructor tag 244");
    assert!(
        format!("{err:#}").contains("tag 244 of heap constructor Big.c244 exceeds 243"),
        "--emit trustir must refuse by name: {err:#}"
    );
}
