// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Pins for the compiled-IR decoder.
//!
//! The exact counts and renderings below were printed by the pinned toolchain
//! itself — the oracle `tests/fixtures/lean/v4.30.0-rc2/oracle/IRCensusOracle.lean`
//! run with `lean` v4.30.0-rc2 — not derived from the decoder under test.

use super::census::CensusRow;
use super::error::LeanIrError;
use super::format::name_to_string;
use super::format_decl::{format_decl, nat_to_string, quote_string};
use super::module_ir::{
    find_module_ir_olean, load_module_ir_at, InterpSource, MainSource, ModuleIr, DECL_MAP_EXT,
    MEASURED_LEAN_VERSION,
};
use super::types;
use crate::expr::BigNat;
use crate::test_support::PINNED_LEAN_REQUIRED;
use clean_kernel::Name;

pub(super) fn pinned_lib() -> std::path::PathBuf {
    crate::pinned_lean_lib_path().expect(PINNED_LEAN_REQUIRED)
}

pub(super) fn parse_module_name(module: &str) -> Result<Name, crate::ImportError> {
    crate::import::legacy_module_name(module)
}

fn load(module: &str) -> ModuleIr {
    let name = parse_module_name(module).expect("module name parses");
    let olean = find_module_ir_olean(&name, &[pinned_lib()])
        .unwrap_or_else(|e| panic!("{module} must resolve: {e}"));
    load_module_ir_at(&name, &olean)
        .unwrap_or_else(|e| panic!("{module} must decode completely: {e}"))
}

fn find<'a>(decls: &'a [types::Decl], name: &str) -> &'a types::Decl {
    decls
        .iter()
        .find(|d| name_to_string(d.name()) == name)
        .unwrap_or_else(|| panic!("{name} is not among the decoded declarations"))
}

// --- Name.toString ----------------------------------------------------------

fn n(components: &[&str]) -> Name {
    components
        .iter()
        .fold(Name::anon(), |p, c| match c.parse() {
            Ok(v) => p.num(v),
            Err(_) => p.str(c),
        })
}

#[test]
fn test_name_to_string_identifiers_are_not_escaped() {
    assert_eq!(
        name_to_string(&n(&["Nat", "add", "_boxed"])),
        "Nat.add._boxed"
    );
    assert_eq!(
        name_to_string(&n(&["_private", "Init", "Prelude", "0", "f"])),
        "_private.Init.Prelude.0.f"
    );
    assert_eq!(name_to_string(&n(&["α", "x'", "h₁"])), "α.x'.h₁");
    assert_eq!(name_to_string(&Name::anon()), "[anonymous]");
}

#[test]
fn test_name_to_string_non_identifiers_are_escaped() {
    assert_eq!(name_to_string(&n(&["Lean", "term_+_"])), "Lean.«term_+_»");
    assert_eq!(name_to_string(&Name::anon().str("")), "«»");
    assert_eq!(name_to_string(&Name::anon().str("a.b")), "«a.b»");
    // A component containing `»` cannot be escaped and prints raw.
    assert_eq!(name_to_string(&Name::anon().str("a»b")), "a»b");
}

#[test]
fn test_name_to_string_inaccessible_and_hygienic_names_print_raw() {
    assert_eq!(name_to_string(&n(&["a+b", "x✝"])), "a+b.x✝");
    assert_eq!(name_to_string(&n(&["a+b", "_hyg", "3"])), "a+b._hyg.3");
    assert_eq!(name_to_string(&n(&["#1", "a+b"])), "#1.a+b");
    assert_eq!(name_to_string(&Name::anon().str("_")), "_");
}

// --- literals ---------------------------------------------------------------

#[test]
fn test_nat_to_string_multi_limb_is_decimal() {
    assert_eq!(nat_to_string(&BigNat::from_u64(0)), "0");
    assert_eq!(
        nat_to_string(&BigNat::from_u64(u64::MAX)),
        "18446744073709551615"
    );
    assert_eq!(
        nat_to_string(&BigNat::from_limbs(vec![0, 1])),
        "18446744073709551616"
    );
    // 2^128 - 1
    assert_eq!(
        nat_to_string(&BigNat::from_limbs(vec![u64::MAX, u64::MAX])),
        "340282366920938463463374607431768211455"
    );
    // 10^19 * 2^64: a zero-padded inner chunk
    assert_eq!(
        nat_to_string(&BigNat::from_limbs(vec![0, 10_000_000_000_000_000_000])),
        "184467440737095516160000000000000000000"
    );
}

#[test]
fn test_quote_string_matches_lean_string_quote() {
    assert_eq!(quote_string("a\"b\\c\nd\te'"), "\"a\\\"b\\\\c\\nd\\te'\"");
    assert_eq!(quote_string("\u{1}\u{7f}é"), "\"\\x01\\x7fé\"");
    assert_eq!(quote_string(""), "\"\"");
}

// --- Init.Prelude, measured against the pinned toolchain --------------------

/// `MOD Init.Prelude fdecl_olean=66 extern_olean=830 fdecl_ir=1127 extern_ir=66
/// extern_attr=67 implemented_by=9 regular_init=0 regular_init_ir=0
/// builtin_init=0` — the oracle's row, `IR_CENSUS_ROOTS=Init.Prelude`.
#[test]
fn test_load_module_ir_init_prelude_counts_equal_pinned_lean() {
    let ir = load("Init.Prelude");
    assert!(ir.is_module, "Init.Prelude is a `module` file");
    assert_eq!(ir.main_source, MainSource::OleanPrivate);
    assert_eq!(ir.interp_source, InterpSource::IrFile);
    assert_eq!(
        CensusRow::from_module(&ir).to_line(),
        "MOD Init.Prelude fdecl_olean=66 extern_olean=830 fdecl_ir=1127 extern_ir=66 \
         extern_attr=67 implemented_by=9 regular_init=0 regular_init_ir=0 builtin_init=0"
    );
}

/// A `Std` module, a `Std` module with `implemented_by` entries, and a `Lean`
/// module with `init` and `builtin_init` entries: the rows the oracle printed
/// for them in the Mathlib-closure census (they resolve to the toolchain's own
/// `lib/lean`, the same files as here).
#[test]
fn test_load_module_ir_std_and_lean_rows_equal_pinned_lean() {
    for expected in [
        "MOD Std.Data.HashMap.Basic fdecl_olean=35 extern_olean=140 fdecl_ir=289 extern_ir=0 \
         extern_attr=0 implemented_by=0 regular_init=0 regular_init_ir=0 builtin_init=0",
        "MOD Std.Tactic.BVDecide.Bitblast.BVExpr.Basic fdecl_olean=0 extern_olean=168 \
         fdecl_ir=266 extern_ir=0 extern_attr=0 implemented_by=12 regular_init=0 \
         regular_init_ir=0 builtin_init=0",
        "MOD Lean.Elab.Tactic.RCases fdecl_olean=0 extern_olean=37 fdecl_ir=523 extern_ir=0 \
         extern_attr=0 implemented_by=0 regular_init=1 regular_init_ir=1 builtin_init=3",
    ] {
        let module = expected.split(' ').nth(1).expect("row names a module");
        assert_eq!(CensusRow::from_module(&load(module)).to_line(), expected);
    }
}

/// `DECL Init.Prelude olean instInhabitedNat` / `… ir instInhabitedNat` /
/// `… ir Nat.add._boxed`, printed by the oracle with `IR_CENSUS_PRINT`.
#[test]
fn test_format_decl_init_prelude_matches_pinned_lean_rendering() {
    let ir = load("Init.Prelude");
    assert_eq!(
        format_decl(find(&ir.olean_decls, "instInhabitedNat")),
        "extern instInhabitedNat : tobj"
    );
    assert_eq!(
        format_decl(find(ir.ir_decls(), "instInhabitedNat")),
        "def instInhabitedNat : tobj :=\n  let x_1 : tagged := 0;\n  ret x_1"
    );
    let boxed = "def Nat.add._boxed (x_1 : tobj) (x_2 : tobj) : tobj :=\n  \
                 let x_3 : tobj := Nat.add x_1 x_2;\n  dec x_2;\n  dec x_1;\n  ret x_3";
    assert_eq!(format_decl(find(&ir.olean_decls, "Nat.add._boxed")), boxed);
    assert_eq!(format_decl(find(ir.ir_decls(), "Nat.add._boxed")), boxed);
}

// --- the `ir_census` fixture family, diffed live against the oracle ---------

use super::census::{run_census, CensusRequest};
use crate::region::CompactedRegion;
use std::path::Path;

/// Run the pinned-Lean census oracle with `imports` added after `import Lean`,
/// `LEAN_PATH = lean_path`, and the given `IR_CENSUS_*` variables. Panics with
/// Lean's stderr on failure — a missing toolchain is a failure, never a skip.
pub(super) fn run_census_oracle(
    lean_path: &Path,
    imports: &[&str],
    vars: &[(&str, &str)],
) -> String {
    let template = crate::test_support::fixture_root().join("oracle/IRCensusOracle.lean");
    let text = std::fs::read_to_string(&template)
        .unwrap_or_else(|e| panic!("cannot read {}: {e}", template.display()));
    let extra: String = imports.iter().map(|m| format!("\nimport {m}")).collect();
    let text = text.replacen("import Lean\n", &format!("import Lean{extra}\n"), 1);
    let dir = tempfile::tempdir().expect("tempdir");
    let script = dir.path().join("Oracle.lean");
    std::fs::write(&script, text).expect("write oracle");
    let out = dir.path().join("oracle.out");
    let lean = crate::pinned_lean_binary().expect(PINNED_LEAN_REQUIRED);
    let output = std::process::Command::new(&lean)
        .current_dir(dir.path())
        .env("LEAN_PATH", lean_path)
        .env("IR_CENSUS_OUT", &out)
        .envs(vars.iter().copied())
        .arg(&script)
        .output()
        .unwrap_or_else(|e| panic!("cannot execute {}: {e}", lean.display()));
    assert!(
        output.status.success() && output.stdout.is_empty(),
        "oracle failed with {}\n--- stdout ---\n{}\n--- stderr ---\n{}",
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::read_to_string(&out).expect("the oracle writes UTF-8 to IR_CENSUS_OUT")
}

fn fixture_request(dir: &Path) -> CensusRequest {
    CensusRequest {
        modules: vec![
            parse_module_name("IrPlain").expect("name"),
            parse_module_name("IrModule").expect("name"),
        ],
        closure: true,
        search_paths: vec![dir.to_path_buf(), pinned_lib()],
        print_decls: Vec::new(),
        print_modules: vec!["IrPlain".into(), "IrModule".into()],
        print_attrs: true,
        jobs: 4,
    }
}

/// The whole census text — every `MOD` row of the fixtures' closure (all of
/// `Init` plus the two fixture modules), the `TOTAL`, every declaration of the
/// two fixture modules rendered, and every attribute / extern-data / sorry
/// line of the closure — equals what the pinned toolchain prints, byte for
/// byte.
#[test]
fn test_run_census_fixture_closure_equals_pinned_lean_oracle() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let lean = run_census_oracle(
        &dir,
        &["IrPlain", "IrModule"],
        &[
            ("IR_CENSUS_ROOTS", "IrPlain,IrModule"),
            ("IR_CENSUS_PRINT_MODULES", "IrPlain,IrModule"),
            ("IR_CENSUS_ATTRS", "1"),
        ],
    );
    let clean = run_census(&fixture_request(&dir)).expect("census runs");
    assert!(
        clean.failures.is_empty(),
        "decode failures: {:?}",
        clean.failures
    );
    assert!(
        clean
            .summary
            .contains(&format!("{} module(s)", clean.modules)),
        "{}",
        clean.summary
    );
    assert!(
        lean.lines().any(|l| l.starts_with("MOD IrPlain "))
            && lean
                .lines()
                .any(|l| l == "DECLEXT IrModule olean modPub opaque"),
        "the oracle output must cover the fixtures:\n{lean}"
    );
    if clean.stdout != lean {
        let first = clean
            .stdout
            .lines()
            .zip(lean.lines())
            .position(|(a, b)| a != b);
        panic!(
            "census differs from pinned Lean ({} vs {} lines); first differing line {first:?}: \
             clean {:?} / lean {:?}",
            clean.stdout.lines().count(),
            lean.lines().count(),
            first.and_then(|i| clean.stdout.lines().nth(i)),
            first.and_then(|i| lean.lines().nth(i)),
        );
    }
}

fn fixture_module(dir: &Path, module: &str) -> ModuleIr {
    let name = parse_module_name(module).expect("name");
    load_module_ir_at(&name, &dir.join(format!("{module}.olean")))
        .unwrap_or_else(|e| panic!("{module} must decode: {e}"))
}

/// A non-`module` file has no `.ir`: its interpreter data IS its `.olean`
/// (`ImportedModule.interpData?`), and the attribute entries decode to the
/// declarations the source names.
#[test]
fn test_load_module_ir_plain_file_reads_ir_from_main_data() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    assert!(
        !dir.join("IrPlain.ir").exists(),
        "a non-module file writes no .ir"
    );
    let ir = fixture_module(&dir, "IrPlain");
    assert!(!ir.is_module);
    assert_eq!(ir.main_source, MainSource::Olean);
    assert_eq!(ir.interp_source, InterpSource::MainData);
    assert_eq!(ir.ir_decls(), ir.olean_decls.as_slice());
    match find(&ir.olean_decls, "nativeFn") {
        types::Decl::Extern { ext, .. } => assert_eq!(
            ext.entries,
            vec![types::ExternEntry::Standard {
                backend: Name::anon().str("all"),
                symbol: "irplain_native".into()
            }]
        ),
        other => panic!("nativeFn must be an extern decl, got {other:?}"),
    }
    assert_eq!(
        ir.implemented_by,
        vec![(Name::anon().str("specFn"), Name::anon().str("implFn"))]
    );
    assert_eq!(ir.regular_init.len(), 1);
    assert_eq!(name_to_string(&ir.regular_init[0].0), "plainRef");
}

/// A `module` file: the `.olean.private` level keeps the `meta` definition's
/// body and turns every other public declaration into an opaque extern; the
/// `.ir` file carries every body, including the private one.
#[test]
fn test_load_module_ir_module_file_splits_meta_closure_and_ir_file() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let ir = fixture_module(&dir, "IrModule");
    assert!(ir.is_module);
    assert_eq!(ir.main_source, MainSource::OleanPrivate);
    assert_eq!(ir.interp_source, InterpSource::IrFile);
    assert!(matches!(
        find(&ir.olean_decls, "modMeta"),
        types::Decl::FDecl { .. }
    ));
    match find(&ir.olean_decls, "modPub") {
        types::Decl::Extern { ext, .. } => {
            assert_eq!(ext.entries, vec![types::ExternEntry::Opaque]);
        }
        other => panic!("modPub must be an opaque extern at the olean level, got {other:?}"),
    }
    assert!(matches!(
        find(ir.ir_decls(), "modPub"),
        types::Decl::FDecl { .. }
    ));
    assert!(matches!(
        find(ir.ir_decls(), "_private.IrModule.0.modPriv"),
        types::Decl::FDecl { .. }
    ));
}

/// Copy a compiled fixture module's files into a fresh directory.
pub(super) fn copy_module(dir: &Path, module: &str, into: &Path) {
    for ext in ["olean", "olean.server", "olean.private", "ir"] {
        let from = dir.join(format!("{module}.{ext}"));
        if from.exists() {
            std::fs::copy(&from, into.join(format!("{module}.{ext}"))).expect("copy fixture");
        }
    }
}

/// File offset of the first `Decl` object of an `.ir` file's `declMapExt`.
fn first_ir_decl_offset(bytes: &[u8]) -> usize {
    let header = crate::header::OleanHeader::parse(bytes).expect("header");
    let region = CompactedRegion::new(bytes, header.base_addr);
    let part = region
        .ir_part_entries(region.root_ptr().expect("root"))
        .expect("entries");
    let array = part.get(DECL_MAP_EXT).expect("declMapExt present");
    let decoder = super::decode::IrDecoder::new(&region);
    let first = decoder.array(array, "declMapExt", 1 << 20).expect("array")[0];
    region.ptr_to_offset(first).expect("offset")
}

/// A `Decl` whose constructor tag is not `fdecl`/`extern` is refused, with the
/// extension named — and the census over it is refused too: the module is
/// listed as failed and no `TOTAL` row is printed.
#[test]
fn test_load_module_ir_corrupt_decl_tag_is_refused() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let tmp = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrModule", tmp.path());
    let ir_path = tmp.path().join("IrModule.ir");
    let mut bytes = std::fs::read(&ir_path).expect("read .ir");
    let at = first_ir_decl_offset(&bytes);
    assert!(bytes[at + 7] <= 1, "the first object is a Decl constructor");
    bytes[at + 7] = 5;
    std::fs::write(&ir_path, &bytes).expect("write .ir");

    let name = parse_module_name("IrModule").expect("name");
    match load_module_ir_at(&name, &tmp.path().join("IrModule.olean")) {
        Err(LeanIrError::InDecl {
            extension, source, ..
        }) => {
            assert_eq!(extension, DECL_MAP_EXT);
            assert!(
                matches!(*source, LeanIrError::Layout { what: "Decl", .. }),
                "expected a Decl layout refusal, got {source}"
            );
        }
        other => panic!("a corrupt Decl tag must be refused, got {other:?}"),
    }

    let report = run_census(&CensusRequest {
        modules: vec![name],
        closure: false,
        search_paths: vec![tmp.path().to_path_buf()],
        jobs: 1,
        ..CensusRequest::default()
    })
    .expect("the census itself runs");
    assert_eq!(report.failures.len(), 1, "{:?}", report.failures);
    assert!(!report.stdout.contains("TOTAL"), "{}", report.stdout);
}

/// Lean's `finalizeImport` throws `missing IR data file` for a `module`
/// without its `.ir`; so does this reader, instead of falling back.
#[test]
fn test_load_module_ir_missing_ir_file_is_refused() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let tmp = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrModule", tmp.path());
    std::fs::remove_file(tmp.path().join("IrModule.ir")).expect("remove .ir");
    let name = parse_module_name("IrModule").expect("name");
    match load_module_ir_at(&name, &tmp.path().join("IrModule.olean")) {
        Err(LeanIrError::MissingFile { path, .. }) => {
            assert_eq!(path.extension().and_then(|e| e.to_str()), Some("ir"));
        }
        other => panic!("a module without its .ir must be refused, got {other:?}"),
    }
}

/// A `module` without its `.olean.private` is refused (Lean: `missing data
/// file`), never read from the exported `.olean` instead.
#[test]
fn test_load_module_ir_missing_private_part_is_refused() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let tmp = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrModule", tmp.path());
    std::fs::remove_file(tmp.path().join("IrModule.olean.private")).expect("remove private");
    let name = parse_module_name("IrModule").expect("name");
    let result = load_module_ir_at(&name, &tmp.path().join("IrModule.olean"));
    assert!(
        matches!(result, Err(LeanIrError::MissingFile { ref path, .. })
            if path.to_string_lossy().ends_with(".olean.private")),
        "got {result:?}"
    );
}

/// The IR layout is measured for exactly one Lean version; a file written by
/// any other is refused before a single object is read.
#[test]
fn test_load_module_ir_other_lean_version_is_refused() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let tmp = tempfile::tempdir().expect("tempdir");
    copy_module(&dir, "IrPlain", tmp.path());
    let path = tmp.path().join("IrPlain.olean");
    let mut bytes = std::fs::read(&path).expect("read");
    let at = bytes
        .windows(MEASURED_LEAN_VERSION.len())
        .position(|w| w == MEASURED_LEAN_VERSION.as_bytes())
        .expect("the header carries the Lean version");
    assert!(at < 88, "the version string is in the v2 header");
    let last = at + MEASURED_LEAN_VERSION.len() - 1;
    bytes[last] = b'9';
    std::fs::write(&path, &bytes).expect("write");
    let name = parse_module_name("IrPlain").expect("name");
    let result = load_module_ir_at(&name, &path);
    assert!(
        matches!(result, Err(LeanIrError::Module { ref detail, .. }) if detail.contains("measured only")),
        "got {result:?}"
    );
}

/// The construct profile of the fixtures reads the flags the renderer never
/// prints: `IrPlain` has nested join points, `case`, a multi-limb literal, a
/// borrowed parameter, scalar stores and an extern.
#[test]
fn test_run_census_profile_counts_fixture_constructs() {
    let dir = crate::test_support::compiled_fixture_dir("ir_census");
    let report = run_census(&CensusRequest {
        modules: vec![parse_module_name("IrPlain").expect("name")],
        closure: false,
        search_paths: vec![dir.clone()],
        jobs: 1,
        ..CensusRequest::default()
    })
    .expect("census runs");
    assert!(report.failures.is_empty(), "{:?}", report.failures);
    assert_eq!(report.modules, 1);
    let profile = &report.profile;
    assert_eq!(profile.count("modules"), 1);
    assert_eq!(profile.count("main_data_olean"), 1);
    assert_eq!(profile.count("modules_module_system"), 0);
    for key in [
        "instr_jdecl",
        "term_case",
        "expr_lit_num_over_u64",
        "expr_lit_str",
        "param_borrowed",
        "instr_sset",
        "instr_uset",
        "expr_is_shared",
        "decl_extern",
        "extern_entry_standard",
    ] {
        assert!(profile.count(key) > 0, "{key} must occur in IrPlain's IR");
    }
    let rendered = profile.render();
    assert!(rendered.contains("PROFILE modules=1\n"), "{rendered}");
    assert!(
        rendered.contains("PROFILE distinct_case_types="),
        "{rendered}"
    );
}

#[test]
fn test_find_module_ir_olean_absent_module_is_refused() {
    let name = parse_module_name("No.Such.Module").expect("name");
    let result = find_module_ir_olean(&name, &[pinned_lib()]);
    assert!(
        matches!(result, Err(LeanIrError::ModuleNotFound { .. })),
        "got {result:?}"
    );
}
