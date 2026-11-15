// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Adversarial pins for the compiled-IR reader, each ground-truthed on the
//! pinned toolchain in the same test: what Lean REFUSES to import is refused
//! here, what it accepts is accepted, and what it prints for shapes the
//! Mathlib-closure differential never meets is printed identically.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use super::census::{run_census, CensusRequest};
use super::error::LeanIrError;
use super::module_ir::{find_module_ir_olean, load_module_ir_at, InterpSource, DECL_MAP_EXT};
use super::tests::{copy_module, parse_module_name, pinned_lib, run_census_oracle};
use crate::region::{is_ptr, CompactedRegion};
use crate::test_support::PINNED_LEAN_REQUIRED;

/// `lean Use.lean` where `Use.lean` is `import <module>`, with `LEAN_PATH`
/// set to `lean_path` in order: the pinned toolchain's verdict on importing
/// `module` from exactly that search path.
fn pinned_lean_import(lean_path: &[&Path], module: &str) -> Output {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("Use.lean"), format!("import {module}\n")).expect("write");
    let joined = std::env::join_paths(lean_path).expect("search path joins");
    let lean = crate::pinned_lean_binary().expect(PINNED_LEAN_REQUIRED);
    Command::new(&lean)
        .current_dir(dir.path())
        .env("LEAN_PATH", joined)
        .arg("Use.lean")
        .output()
        .unwrap_or_else(|e| panic!("cannot execute {}: {e}", lean.display()))
}

fn assert_lean_refuses(output: &Output, needle: &str) {
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        !output.status.success() && stdout.contains(needle),
        "pinned Lean must refuse with `{needle}`; exit {}, stdout:\n{stdout}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stderr)
    );
}

fn assert_lean_accepts(output: &Output) {
    assert!(
        output.status.success(),
        "pinned Lean must accept; exit {}, stdout:\n{}\nstderr:\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// The `IrAdv` fixture carries what the Mathlib closure never does — `adhoc`
/// and `inline` extern entries, a two-entry `@[extern]`, `sorryDep?` in a
/// non-`module` file, `Nat` literals at the tagged/MPZ boundary (2^63 - 1,
/// 2^63, 2^64), a string literal with NUL/CR/DEL and `»«`, `float32`, and
/// names that need escaping, one of them containing a NEWLINE. Its whole
/// census text (rows, every declaration rendered, every attribute line)
/// equals the pinned toolchain's byte for byte. The newline name is the arm
/// that fails when `Layout::text` pushes a text verbatim: Lean breaks it at
/// the current nesting (`«line` / `  break» x_1;`).
#[test]
fn test_run_census_adv_fixture_equals_pinned_lean_byte_for_byte() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let lean = run_census_oracle(
        &dir,
        &["IrAdv"],
        &[
            ("IR_CENSUS_ROOTS", "IrAdv"),
            ("IR_CENSUS_PRINT_MODULES", "IrAdv"),
            ("IR_CENSUS_ATTRS", "1"),
        ],
    );
    for needle in [
        "ATTR IrAdv extern adhocFn adhoc all",
        "ATTR IrAdv extern twoEntries inline c \"lean_box(#1)\" | standard cpp \"cppSym\"",
        "DECLSORRY IrAdv olean callsSorry usesSorry",
        "  let x_1 : tobj := 9223372036854775808;",
        "  let x_1 : tagged := 9223372036854775807;",
        "\n  break» x_1;\n",
    ] {
        assert!(
            lean.contains(needle),
            "the oracle output must exercise {needle:?}:\n{lean}"
        );
    }
    let clean = run_census(&CensusRequest {
        modules: vec![parse_module_name("IrAdv").expect("name")],
        closure: true,
        search_paths: vec![dir.clone(), pinned_lib()],
        print_modules: vec!["IrAdv".into()],
        print_attrs: true,
        jobs: 4,
        ..CensusRequest::default()
    })
    .expect("census runs");
    assert!(clean.failures.is_empty(), "{:?}", clean.failures);
    if clean.stdout != lean {
        let first = clean
            .stdout
            .lines()
            .zip(lean.lines())
            .position(|(a, b)| a != b);
        panic!(
            "census differs from pinned Lean; first differing line {first:?}: clean {:?} / lean {:?}",
            first.and_then(|i| clean.stdout.lines().nth(i)),
            first.and_then(|i| lean.lines().nth(i)),
        );
    }
}

/// Lean's `findOLean` (`SearchPath.findWithExt`) picks the FIRST search-path
/// entry holding the module's root package directory and never looks
/// further: with `LEAN_PATH=A:B`, an empty `A/IrPlain/` and the module at
/// `B/IrPlain.olean`, the pinned toolchain refuses `import IrPlain`
/// (`object file … does not exist`) and accepts it with `B:A`. The census
/// must agree in both orders.
#[test]
fn test_find_module_ir_olean_first_root_package_entry_decides_like_lean() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let tmp = tempfile::tempdir().expect("tempdir");
    let (a, b) = (tmp.path().join("A"), tmp.path().join("B"));
    std::fs::create_dir_all(a.join("IrPlain")).expect("mkdir A/IrPlain");
    std::fs::create_dir_all(&b).expect("mkdir B");
    copy_module(&dir, "IrPlain", &b);

    assert_lean_refuses(
        &pinned_lean_import(&[a.as_path(), b.as_path()], "IrPlain"),
        "does not exist",
    );
    assert_lean_accepts(&pinned_lean_import(&[b.as_path(), a.as_path()], "IrPlain"));

    let name = parse_module_name("IrPlain").expect("name");
    match find_module_ir_olean(&name, &[a.clone(), b.clone()]) {
        Err(LeanIrError::MissingFile { path, .. }) => assert_eq!(path, a.join("IrPlain.olean")),
        other => panic!("A shadows B for the root package `IrPlain`; got {other:?}"),
    }
    assert_eq!(
        find_module_ir_olean(&name, &[b.clone(), a.clone()]).expect("B decides"),
        b.join("IrPlain.olean")
    );
    // The verb's own resolution path refuses the census, not only the helper.
    let refused = run_census(&CensusRequest {
        modules: vec![name],
        closure: false,
        search_paths: vec![a, b, pinned_lib()],
        jobs: 1,
        ..CensusRequest::default()
    });
    assert!(
        matches!(refused, Err(LeanIrError::MissingFile { .. })),
        "got {refused:?}"
    );
}

/// Lean's `loadIR?` reads a `.ir` beside ANY module's `.olean` when one is
/// present, even though `interpData?` then ignores it for a non-`module`
/// file: a `.ir` whose header does not read fails the import, one that
/// reads is accepted and unused. Both halves measured on the pinned
/// toolchain with `IrPlain` (a non-`module` file).
#[test]
fn test_load_module_ir_non_module_sibling_ir_is_header_checked_like_lean() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let name = parse_module_name("IrPlain").expect("name");

    let garbage = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrPlain", garbage.path());
    std::fs::write(garbage.path().join("IrPlain.ir"), b"garbage").expect("write .ir");
    assert_lean_refuses(
        &pinned_lean_import(&[garbage.path()], "IrPlain"),
        "invalid header",
    );
    let result = load_module_ir_at(&name, &garbage.path().join("IrPlain.olean"));
    assert!(
        result.is_err(),
        "a sibling .ir Lean cannot read must be refused, got {result:?}"
    );

    let foreign = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrPlain", foreign.path());
    std::fs::copy(dir.join("IrModule.ir"), foreign.path().join("IrPlain.ir")).expect("copy .ir");
    assert_lean_accepts(&pinned_lean_import(&[foreign.path()], "IrPlain"));
    let ir = load_module_ir_at(&name, &foreign.path().join("IrPlain.olean"))
        .expect("a readable sibling .ir is accepted");
    assert_eq!(ir.interp_source, InterpSource::MainData);
    assert_eq!(ir.ir_decls(), ir.olean_decls.as_slice());
}

/// A `module` without its `.olean.server` is refused: Lean's
/// `findOLeanParts` then never reaches the `.olean.private` part and the
/// import fails with `missing data file` (measured).
#[test]
fn test_load_module_ir_missing_server_part_is_refused_like_lean() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let tmp = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrModule", tmp.path());
    std::fs::remove_file(tmp.path().join("IrModule.olean.server")).expect("remove server");
    assert_lean_refuses(
        &pinned_lean_import(&[tmp.path()], "IrModule"),
        "missing data file",
    );
    let name = parse_module_name("IrModule").expect("name");
    let result = load_module_ir_at(&name, &tmp.path().join("IrModule.olean"));
    assert!(
        matches!(result, Err(LeanIrError::MissingFile { ref path, .. })
            if path.to_string_lossy().ends_with(".olean.server")),
        "got {result:?}"
    );
}

/// The file offset of the continuation field of the first `fdecl` whose body
/// opens with a `vdecl`, in the `declMapExt` entries of a non-`module`
/// `.olean`, together with that `vdecl`'s own pointer.
fn first_vdecl_continuation(bytes: &[u8]) -> (usize, u64) {
    let header = crate::header::OleanHeader::parse(bytes).expect("header");
    let region = CompactedRegion::new(bytes, header.base_addr);
    let part = region
        .ir_part_entries(region.root_ptr().expect("root"))
        .expect("entries");
    let array = part.get(DECL_MAP_EXT).expect("declMapExt present");
    let decoder = super::decode::IrDecoder::new(&region);
    for decl in decoder.array(array, "declMapExt", 1 << 20).expect("array") {
        let at = region.ptr_to_offset(decl).expect("decl offset");
        if region.read_header_at(at).expect("decl header").tag != 0 {
            continue;
        }
        let body = region.read_u64_at(at + 8 + 8 * 3).expect("body field");
        if !is_ptr(body) {
            continue;
        }
        let body_at = region.ptr_to_offset(body).expect("body offset");
        let body_header = region.read_header_at(body_at).expect("body header");
        if body_header.tag == 0 && body_header.other == 4 {
            return (body_at + 8 + 8 * 3, body);
        }
    }
    panic!("no fdecl body opens with a vdecl")
}

/// A `FnBody` chain that loops back on itself (a corrupt or crafted file) is
/// refused. Lean's compactor writes every object after the objects it points
/// to, so a genuine continuation always sits below its instruction; before
/// that was required, the flattening loop followed the cycle forever, growing
/// its instruction vector until memory ran out.
#[test]
fn test_load_module_ir_cyclic_body_chain_is_refused() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let tmp = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrPlain", tmp.path());
    let path: PathBuf = tmp.path().join("IrPlain.olean");
    let mut bytes = std::fs::read(&path).expect("read .olean");
    let (field, vdecl) = first_vdecl_continuation(&bytes);
    bytes[field..field + 8].copy_from_slice(&vdecl.to_le_bytes());
    std::fs::write(&path, &bytes).expect("write .olean");

    let name = parse_module_name("IrPlain").expect("name");
    match load_module_ir_at(&name, &path) {
        Err(LeanIrError::InDecl {
            extension, source, ..
        }) => {
            assert_eq!(extension, DECL_MAP_EXT);
            assert!(
                matches!(*source, LeanIrError::Layout { what: "FnBody", ref detail, .. }
                    if detail.contains("does not precede")),
                "expected the continuation-order refusal, got {source}"
            );
        }
        other => panic!("a cyclic body chain must be refused, got {other:?}"),
    }
}

/// Run `oracle/IRFlagsOracle.lean` with the pinned binary over the closure of
/// `roots` (found on `lean_path`) and parse its `FLAGS k=v …` line.
fn run_flags_oracle(lean_path: &Path, roots: &[&str]) -> Vec<(String, usize)> {
    let template = crate::test_support::fixture_root().join("oracle/IRFlagsOracle.lean");
    let text = std::fs::read_to_string(&template)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", template.display()));
    let extra: String = roots.iter().map(|m| format!("\nimport {m}")).collect();
    let text = text.replacen("import Lean\n", &format!("import Lean{extra}\n"), 1);
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("Flags.lean"), text).expect("write oracle");
    let lean = crate::pinned_lean_binary().expect(PINNED_LEAN_REQUIRED);
    let output = Command::new(&lean)
        .current_dir(dir.path())
        .env("LEAN_PATH", lean_path)
        .env("IR_FLAGS_ROOTS", roots.join(","))
        .arg("Flags.lean")
        .output()
        .unwrap_or_else(|e| panic!("cannot execute {}: {e}", lean.display()));
    assert_lean_accepts(&output);
    let stdout = String::from_utf8(output.stdout).expect("UTF-8");
    let line = stdout
        .lines()
        .find_map(|l| l.strip_prefix("FLAGS "))
        .unwrap_or_else(|| panic!("no FLAGS line in:\n{stdout}"));
    line.split(' ')
        .map(|kv| {
            let (k, v) = kv.split_once('=').expect("k=v");
            (k.to_owned(), v.parse().expect("count"))
        })
        .collect()
}

/// What the census's byte-exact declaration diff cannot see, because Lean's
/// `IR.Decl` formatter never prints it — the `c` and `persistent` flags of
/// `inc`/`dec`, `Param.borrow`, `CtorInfo.size` and `case`'s type id — is
/// counted by the pinned toolchain itself (`oracle/IRFlagsOracle.lean`) over
/// the fixtures' closure (all of `Init`, a `module` file at both levels) and
/// equals the decoder's profile. `rc_known_object` and `rc_persistent` differ
/// there, so decoding the two `Bool` scalars in swapped order fails this.
#[test]
fn test_run_census_profile_unrendered_fields_equal_pinned_lean() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let roots = ["IrPlain", "IrModule", "IrAdv"];
    let lean = run_flags_oracle(&dir, &roots);
    let report = run_census(&CensusRequest {
        modules: roots
            .iter()
            .map(|m| parse_module_name(m).expect("name"))
            .collect(),
        closure: true,
        search_paths: vec![dir.clone(), pinned_lib()],
        jobs: 4,
        ..CensusRequest::default()
    })
    .expect("census runs");
    assert!(report.failures.is_empty(), "{:?}", report.failures);
    let rendered = report.profile.render();
    let clean = |key: &str| -> usize {
        rendered
            .lines()
            .find_map(|l| l.strip_prefix(&format!("PROFILE {key}=")))
            .map_or(0, |v| v.parse().expect("count"))
    };
    assert!(
        lean.iter().any(|(k, v)| k == "rc_known_object" && *v > 0)
            && lean
                .iter()
                .find(|(k, _)| k == "rc_known_object")
                .map(|(_, v)| v)
                != lean
                    .iter()
                    .find(|(k, _)| k == "rc_persistent")
                    .map(|(_, v)| v),
        "the closure must tell the two rc flags apart: {lean:?}"
    );
    for (key, want) in &lean {
        assert_eq!(clean(key), *want, "{key}: clean vs pinned Lean");
    }
}
