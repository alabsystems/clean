// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean extract` and `@[implemented_by]`: every lane that compiles the
//! closure (C, wasm, the TV certificate) promises the KERNEL value, and since
//! `docs/DECISIONS.md` R149 it lowers the closure at
//! `clean_compiler::CodeMeaning::KernelValue`: no reference is substituted by
//! an implementation, so a closure that reaches an `@[implemented_by]`
//! declaration compiles its logical body and extracts the kernel value. Until
//! R149 such a closure was refused (`extract-implemented-by`), and so was every
//! root of a file with a late `attribute [implemented_by]` command
//! (`native-implemented-by-order`). The native lanes still substitute and
//! refuse as before (`clean_native`'s `compile_implemented_by_tests`). A child
//! of `cmd_extract::tests::backend`, split out to keep that file under the
//! 500-line bound.

use super::*;

/// `fast` differs from `slow`'s kernel value at a battery point (`7`, where
/// it returns `0` and the kernel `8`), so a closure compiled through `fast`
/// fails the differential instead of passing it by luck.
const NAT_SRC: &str = "\
def fast (n : Nat) : Nat := if n = 7 then 0 else n + 1
@[implemented_by fast] def slow (n : Nat) : Nat := n + 1
def f (n : Nat) : Nat := slow n
def g (n : Nat) : Nat := n + 1
";

/// As [`NAT_SRC`], at the `UInt32` battery point `(41, 41)`. `slow` is
/// spelled with `UInt32.add` over its parameters and no literal, the shape the
/// wasm lane lowers (`test_extract_wasm_lowers_uintw_arithmetic_to_native_instructions`).
const U32_SRC: &str = "\
def fast (a b : UInt32) : UInt32 := if a = 41 then 0 else UInt32.add a b
@[implemented_by fast] def slow (a b : UInt32) : UInt32 := UInt32.add a b
def f (a b : UInt32) : UInt32 := slow a b
def g (a b : UInt32) : UInt32 := UInt32.add (UInt32.mul a b) b
";

/// `src` written to a fresh directory, and the arguments that extract `decl`
/// from it on `backend`.
fn extract_args(
    src: &str,
    decl: &str,
    backend: ExtractBackend,
) -> (tempfile::TempDir, ExtractArgs) {
    let tmp = tempfile::Builder::new()
        .prefix("clean-extract-implby-")
        .tempdir()
        .expect("scratch dir");
    let src_path = tmp.path().join("implby.lean");
    std::fs::write(&src_path, src).expect("write source");
    let args = ExtractArgs {
        file: src_path,
        decl: decl.to_string(),
        out: tmp.path().join("out"),
        backend,
        keep_temp: false,
    };
    (tmp, args)
}

/// What the C lane's battery binary prints for `args`: the closure selected
/// and emitted exactly as `handle_extract_c` does (`select_and_emit`), linked
/// with its battery driver and run. Each line is one battery point's result.
fn c_battery_stdout(args: &ExtractArgs) -> (String, Vec<String>) {
    let (c_source, env) = select_and_emit(args).unwrap_or_else(|e| panic!("emit: {e:#}"));
    let sig = extraction_gate(&env, &Name::from_string(&args.decl)).expect("gate");
    let shims = native_build::select_shims_for_c_text(&c_source).expect("shims");
    let build = tempfile::tempdir().expect("build dir");
    let driver = render_battery_driver(&args.decl, &sig, &build_battery(&sig), &shims, &c_source);
    let exe = native_build::build_extract_executable(build.path(), &shims, &c_source, &driver)
        .expect("link the battery binary");
    let out = Command::new(&exe).output().expect("run the battery binary");
    assert!(out.status.success(), "battery binary exited nonzero");
    let lines = String::from_utf8_lossy(&out.stdout)
        .lines()
        .map(str::to_owned)
        .collect();
    (c_source, lines)
}

/// `@[implemented_by]` changes which body COMPILED code runs, never the
/// kernel meaning extraction promises, so the C and wasm lanes compile the
/// declaration's logical body. The C lane extracts `f`, which reaches `slow`:
/// its battery binary prints exactly the kernel value at every point (`slow 7
/// = 8`; `fast 7` would print `0`). Both lanes extract `slow` itself. The
/// wasm lane compiles only call-free code, so it refuses `f` for its call to
/// `slow` (measured 2026-10-20: "call to `slow` is outside the Wasm
/// fragment"), and that refusal is the fragment's, never an
/// `@[implemented_by]` one.
#[test]
fn test_extract_compiles_the_kernel_value_through_a_reached_implemented_by() {
    let (_tmp, args) = extract_args(NAT_SRC, "f", ExtractBackend::C);
    let (c, stdout) = c_battery_stdout(&args);
    assert_eq!(stdout, ["1", "2", "3", "4", "8", "13", "64"], "{c}");
    assert!(
        c.contains("l_slow") && !c.contains("l_fast"),
        "the closure lowers `slow`'s own value and never its implementation:\n{c}"
    );

    // A `Nat` parameter gives 7 battery points; two `UInt32` ones give 8 (7
    // and the crossed point, `build_battery`).
    for (backend, src, decl, points) in [
        (ExtractBackend::C, NAT_SRC, "f", 7),
        (ExtractBackend::C, NAT_SRC, "slow", 7),
        (ExtractBackend::Wasm, U32_SRC, "slow", 8),
    ] {
        let (_tmp, args) = extract_args(src, decl, backend);
        extract(&args).unwrap_or_else(|e| {
            panic!("{backend:?}: `{decl}` must extract the kernel value of `slow`: {e:#}")
        });
        let manifest: serde_json::Value = serde_json::from_str(
            &std::fs::read_to_string(args.out.join("manifest.json")).expect("manifest"),
        )
        .expect("manifest is JSON");
        assert!(
            manifest["differential"]
                .as_str()
                .is_some_and(|d| d.starts_with("PASSED")),
            "{backend:?} `{decl}`: {manifest}"
        );
        assert_eq!(
            manifest["battery_points"], points,
            "{backend:?} `{decl}`: {manifest}"
        );
    }

    let (_tmp, args) = extract_args(U32_SRC, "f", ExtractBackend::Wasm);
    let refusal = format!(
        "{:#}",
        extract(&args).expect_err("the wasm lane compiles no call")
    );
    assert!(
        refusal.contains("call to `slow` is outside the Wasm fragment")
            && !refusal.contains("implemented"),
        "{refusal}"
    );
}

/// The control: in the SAME file, a closure that reaches no
/// `@[implemented_by]` (`g`) extracts on both lanes, as before R149.
#[test]
fn test_extract_closure_without_a_binding_still_extracts() {
    for (backend, src) in [
        (ExtractBackend::C, NAT_SRC),
        (ExtractBackend::Wasm, U32_SRC),
    ] {
        let (_tmp, args) = extract_args(src, "g", backend);
        extract(&args).unwrap_or_else(|e| {
            panic!("{backend:?}: `g` reaches no implemented_by and must extract: {e:#}")
        });
        assert!(
            args.out.join("manifest.json").exists(),
            "{backend:?}: a successful extraction writes its manifest"
        );
    }
}

/// The TV certificate lane selects and lowers its closure the same way
/// (`tv_certificate_entry`, `select_lcnf_decl_kernel_meaning`, the pipeline
/// at `CodeMeaning::KernelValue`), so it certifies `f` with `slow`, compared
/// with its KERNEL definition, in the certified closure, and the control `g`.
/// The status is pinned: `tv_certificate_entry` answers `unattempted` for
/// every lowering error but a refused translation, an `@[implemented_by]`
/// substitution or refusal included, so accepting that status would let this
/// test pass on the regression it guards. So are the certified closure and
/// the count of closure members outside the certificate's fragment, as
/// measured on 2026-10-21.
#[cfg(feature = "trust-ir-backend")]
#[test]
fn test_extract_tv_lane_lowers_the_kernel_value_through_a_reached_implemented_by() {
    for (decl, closure, skipped) in [("f", &["f", "slow"][..], 1), ("g", &["g"][..], 2)] {
        let (_tmp, args) = extract_args(U32_SRC, decl, ExtractBackend::C);
        let entry = tv_certificate_entry(&args)
            .unwrap_or_else(|e| panic!("`{decl}`: the TV lane must not refuse: {e:#}"));
        assert_eq!(
            entry["status"].as_str(),
            Some("certified"),
            "{decl}: {entry}"
        );
        let mut certified: Vec<&str> = entry["closure_certified"]
            .as_array()
            .unwrap_or_else(|| panic!("{decl}: a certified entry lists its closure: {entry}"))
            .iter()
            .filter_map(serde_json::Value::as_str)
            .collect();
        certified.sort_unstable();
        assert_eq!(certified, closure, "{decl}: {entry}");
        assert_eq!(
            entry["closure_skipped"].as_u64(),
            Some(skipped),
            "{decl}: {entry}"
        );
    }
}

/// A file with an `attribute [implemented_by]` command written after code
/// that reaches what it binds: the native lanes refuse every root of it
/// (`native-implemented-by-order`), because which body that code runs is
/// Lean's inliner's choice. Extraction compiles the kernel value, which does
/// not depend on it, so since R149 it extracts both a closure that reaches no
/// binding (`g`) and the code compiled before the command (`caller`, whose
/// kernel value is `slow n = n + 2`; Lean may run either body).
#[test]
fn test_extract_is_not_refused_by_the_order_record() {
    const LATE: &str = "\
def fast (n : Nat) : Nat := n + 1
def slow (n : Nat) : Nat := n + 2
def caller (n : Nat) : Nat := slow n
attribute [implemented_by fast] slow
def g (n : Nat) : Nat := n + 1
";
    let (_tmp, args) = extract_args(LATE, "caller", ExtractBackend::C);
    let (c, stdout) = c_battery_stdout(&args);
    assert_eq!(stdout, ["2", "3", "4", "5", "9", "14", "65"], "{c}");
    for decl in ["g", "caller"] {
        let (_tmp, args) = extract_args(LATE, decl, ExtractBackend::C);
        extract(&args).unwrap_or_else(|e| panic!("`{decl}` must extract: {e:#}"));
        assert!(
            args.out.join("manifest.json").exists(),
            "`{decl}`: a successful extraction writes its manifest"
        );
    }
}
