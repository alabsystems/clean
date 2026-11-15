// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean compile --emit trustir-bin --link-artifact` (WS6.8): the import
//! producer measured THROUGH the production path, from real Lean source.
//!
//! The library/client pair is the proof program's standalone-lane fixture
//! (`parta/Lib.lean`, `parta/Use.lean`, 2026-09-17), with one addition on each
//! side: `Lib.libRoot` is the compile root whose closure puts
//! `addmul`/`pick`/`program` into `lib.bin`, and `Use.useLib` CALLS them —
//! the original `Use.lean` only cites `Lib` from theorems, so a compile of it
//! has nothing to import.
//!
//! Before WS6.8 `Use.lean`'s compile re-defined every `Lib` constant it
//! reached next to its own, so no digest-authenticated edge existed between
//! the two modules (F-093, `Module.imports = 0`).

use super::*;

use std::path::{Path, PathBuf};

use clean_compiler::emit_trust_ir::{
    deserialize_module_bytes, module_stable_digest_string, serialize_module_bytes,
};
use clean_compiler::emit_trust_ir_link::{
    linked_verdict, FuncTy, Function, LinkRefusal, Module, Ty,
};

/// `parta/Lib.lean` plus the compile root `libRoot`.
fn lib_source(addmul_body: &str) -> String {
    format!(
        "def addmul (a b : UInt64) : UInt64 := {addmul_body}\n\
         def pick (a b : UInt64) : UInt64 := a\n\
         def lit8 (a : UInt8) : UInt8 := a + 200\n\
         def program : UInt64 := 48\n\
         theorem pick_eq (a b : UInt64) : pick a b = a := rfl\n\
         def libRoot (a b : UInt64) : UInt64 := addmul (pick a b) program\n"
    )
}

/// `parta/Use.lean` plus `useLib`, which calls into `Lib`.
const USE_SOURCE: &str = "import Lib\n\
    def keepLeft (a b : UInt64) : UInt64 := a\n\
    theorem keepLeft_is_pick (a b : UInt64) : keepLeft a b = pick a b := rfl\n\
    theorem keepLeft_eq (a b : UInt64) : keepLeft a b = a := pick_eq a b\n\
    def useLib (a b : UInt64) : UInt64 := addmul (pick a b) program + keepLeft a b\n";

const HONEST_ADDMUL: &str = "a * b + a";

/// `clean compile -O1 --emit trustir-bin <file> --decl <decl> -o <out>
/// [--link-artifact <links>..]`.
///
/// `-O1`, not `-O0`: at `-O0` the known-instance rule (WS6.4) does not run,
/// so `a * b + a` stays a boxed `HMul`/`HAdd` class-method call and the
/// kernel TV pass certifies NO fixed-width root
/// (`test_ws6_4_battery_tv_status_by_level`) — `addmul` would then be an
/// identity-only import on every side and the source binding would never be
/// exercised. Both sides of every pair compile at the same level.
fn trustir_bin(file: &Path, decl: &str, out: &Path, links: &[&Path]) -> anyhow::Result<()> {
    handle_compile_command(CompileArgs {
        file: Some(file.to_path_buf()),
        decl: Some(decl.to_owned()),
        emit: EmitFormat::TrustirBin,
        opt_level: 1,
        output: Some(out.to_path_buf()),
        link_artifact: links.iter().map(|p| p.to_path_buf()).collect(),
    })
}

/// A project directory holding `Lib.lean` (with `addmul_body`) and `Use.lean`.
fn project(addmul_body: &str) -> tempfile::TempDir {
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("Lib.lean"), lib_source(addmul_body)).expect("write Lib");
    std::fs::write(dir.path().join("Use.lean"), USE_SOURCE).expect("write Use");
    dir
}

/// `clean compile --emit trustir-bin Lib.lean --decl libRoot -o <dir>/lib.bin`.
fn build_lib(dir: &Path) -> PathBuf {
    let lib = dir.join("lib.bin");
    trustir_bin(&dir.join("Lib.lean"), "libRoot", &lib, &[]).expect("Lib compiles");
    lib
}

fn read_module(path: &Path) -> Module {
    deserialize_module_bytes(&std::fs::read(path).expect("artifact exists")).expect("decodes")
}

fn digest(module: &Module) -> String {
    module_stable_digest_string(module).expect("wire identity")
}

/// Every function of `module` carrying `symbol`.
fn named<'m>(module: &'m Module, symbol: &str) -> Vec<&'m Function> {
    module
        .functions
        .iter()
        .filter(|f| f.name == symbol)
        .collect()
}

/// Does `module` carry a `Certified` obligation scoped to its `symbol`?
fn certified(module: &Module, symbol: &str) -> bool {
    let Some(f) = named(module, symbol).first().map(|f| f.id) else {
        return false;
    };
    module
        .proof_obligations
        .iter()
        .any(|o| format!("{:?}", o.status) == "Certified" && o.function == Some(f))
}

/// Rendered certificates whose evidence inherits across an import.
fn external_inheritances(module: &Module) -> Vec<String> {
    module
        .proof_certificates
        .iter()
        .map(|c| format!("{:?}", c.evidence))
        .filter(|e| e.contains("InheritedFromCallee") && e.contains("external: Some"))
        .collect()
}

/// GAP row `GENERAL.import.digest_row` (PRODUCER-GAP -> PASS, WS6.8).
///
/// `use.bin`, compiled against `lib.bin`, carries ONE import row whose digest
/// is the one `lib.bin`'s own compile measured, re-embeds none of the
/// `addmul`/`pick`/`program` bodies (each is a body-less declaration), still
/// compiles its own `keepLeft`, inherits the far proof for the certified
/// `addmul`, and `validate_linked_module` — the call `trust-ir validate
/// --link use.bin lib.bin` makes — re-earns every row against `lib.bin`.
///
/// NEGATIVE TWIN: one byte of `lib.bin`'s `addmul` body flipped. The recorded
/// digest no longer names it, and linked validation refuses by name
/// (`ImportUnavailable` for import 0).
#[test]
fn general_import_digest_row() {
    let dir = project(HONEST_ADDMUL);
    let lib_path = build_lib(dir.path());
    let lib = read_module(&lib_path);
    for symbol in ["addmul", "pick", "program", "libRoot"] {
        let found = named(&lib, symbol);
        assert!(
            found.len() == 1 && !found[0].is_declaration(),
            "lib.bin must DEFINE `{symbol}`: {:?}",
            lib.functions.iter().map(|f| &f.name).collect::<Vec<_>>()
        );
    }
    assert!(
        certified(&lib, "addmul"),
        "lib.bin's addmul must itself be kernel-certified, or the inheritance below \
         proves nothing"
    );

    let use_path = dir.path().join("use.bin");
    trustir_bin(
        &dir.path().join("Use.lean"),
        "useLib",
        &use_path,
        &[&lib_path],
    )
    .expect("Use compiles against lib.bin");
    let client = read_module(&use_path);

    // One import row, and its digest is the one lib.bin's compile printed.
    assert_eq!(client.imports.len(), 1, "one artifact used, one row");
    assert_eq!(client.imports[0].digest.to_string(), digest(&lib));
    assert_eq!(client.imports[0].name, "lib");

    // Nothing of Lib is re-embedded; the client's own constant is compiled.
    for symbol in ["addmul", "pick", "program"] {
        let found = named(&client, symbol);
        assert!(
            found.len() == 1 && found[0].is_declaration(),
            "use.bin must DECLARE, not define, `{symbol}`"
        );
    }
    assert!(
        named(&client, "libRoot").is_empty(),
        "unreached, not declared"
    );
    // Nor any AUXILIARY function the client's pipeline generated from an
    // imported constant (`l_addmul___boxed`, ...): no symbol is DEFINED by
    // both modules, which would also be a duplicate definition at native
    // link time.
    let twice: Vec<&str> = client
        .functions
        .iter()
        .filter(|f| !f.is_declaration())
        .filter(|f| named(&lib, &f.name).iter().any(|g| !g.is_declaration()))
        .map(|f| f.name.as_str())
        .collect();
    assert!(twice.is_empty(), "defined by both modules: {twice:?}");
    let keep_left = named(&client, "keepLeft");
    assert!(
        keep_left.len() == 1 && !keep_left[0].is_declaration(),
        "the client's own `keepLeft` is compiled into it"
    );
    // WS6.8: review — the import is USED: the client's root CALLS the
    // declaration, so its `addmul` is the artifact's definition at link time,
    // not a copy of the client's own elaboration spliced into `useLib` (an
    // inlined body would leave the import row decorative).
    let use_lib = named(&client, "useLib");
    assert!(use_lib.len() == 1 && !use_lib[0].is_declaration());
    let call_addmul = format!("Call {{ callee: {:?},", named(&client, "addmul")[0].id);
    assert!(
        format!("{:?}", use_lib[0].blocks).contains(&call_addmul),
        "useLib must call the imported addmul ({call_addmul}): {:?}",
        use_lib[0].blocks
    );

    // The certified `addmul` is inherited across the import, not re-proved.
    let inherited = external_inheritances(&client);
    assert!(
        inherited.iter().any(|e| e.contains("symbol: \"addmul\"")),
        "addmul's far proof must be inherited: {inherited:?}"
    );

    // The consumer's own check re-earns every row.
    let verdict = linked_verdict(&client, std::slice::from_ref(&lib));
    assert!(verdict.is_empty(), "{verdict:?}");

    // --- negative twin: one byte of lib.bin's `addmul` body, flipped. -------
    let bytes = std::fs::read(&lib_path).expect("lib.bin");
    let body = |m: &Module| format!("{:?}", named(m, "addmul")[0].blocks);
    let original_body = body(&lib);
    let mutated = (0..bytes.len())
        .find_map(|i| {
            let mut flipped = bytes.clone();
            flipped[i] ^= 0x01;
            let module = deserialize_module_bytes(&flipped).ok()?;
            let changed = named(&module, "addmul").len() == 1 && body(&module) != original_body;
            changed.then_some(module)
        })
        .expect("some one-byte flip of lib.bin changes addmul's body and still decodes");
    assert_ne!(digest(&mutated), digest(&lib), "the flip moves the digest");
    let refused = linked_verdict(&client, std::slice::from_ref(&mutated));
    assert!(
        refused
            .iter()
            .any(|e| e.starts_with("ImportUnavailable { import: 0,")),
        "the recorded digest must not authenticate the flipped artifact: {refused:?}"
    );
}

/// MUTATION CONTROL: `lib.bin` built from a `Lib.lean` whose `addmul` is
/// `a * b - a` — same symbol, same signature, honestly kernel-certified
/// against its OWN body. The client means `a * b + a`, so `use.bin` records
/// the identity row and NO proof row for `addmul`: the far certificate's
/// comparand is not the client's elaboration of the symbol.
#[test]
fn a_lib_certified_against_a_different_body_backs_no_proof_row() {
    let other = project("a * b - a");
    let other_lib = build_lib(other.path());
    let lib = read_module(&other_lib);
    assert!(
        certified(&lib, "addmul"),
        "the other body must itself be kernel-certified, or this proves nothing"
    );

    let dir = project(HONEST_ADDMUL);
    let use_path = dir.path().join("use.bin");
    trustir_bin(
        &dir.path().join("Use.lean"),
        "useLib",
        &use_path,
        &[&other_lib],
    )
    .expect("identity rows are still honest, so the compile succeeds");
    let client = read_module(&use_path);
    assert_eq!(client.imports.len(), 1, "the identity row is written");
    assert_eq!(client.imports[0].digest.to_string(), digest(&lib));
    assert!(named(&client, "addmul")[0].is_declaration());
    let inherited = external_inheritances(&client);
    assert!(
        !inherited.iter().any(|e| e.contains("symbol: \"addmul\"")),
        "NO proof row may back the client's addmul with a proof about another body: \
         {inherited:?}"
    );
    assert!(linked_verdict(&client, std::slice::from_ref(&lib)).is_empty());
}

/// MUTATION CONTROL: `lib.bin` as a dependency built under a different boxing
/// configuration would carry it — `addmul` at the boxed `fn(ptr, ptr) ->
/// (ptr)` instead of `fn(u64, u64) -> (u64)`. The client's call sites are
/// shaped against its own lowering, so the compile is REFUSED by name
/// (`CallShapeDisagreesWithFarSignature`) and nothing is written: the call is
/// never silently re-boxed, and no module whose call site disagrees with the
/// far `FuncTy` exists.
#[test]
fn a_lib_built_under_a_different_boxing_refuses_the_compile() {
    let dir = project(HONEST_ADDMUL);
    let lib_path = build_lib(dir.path());
    let mut lib = read_module(&lib_path);
    let boxed = lib
        .add_func_type(FuncTy {
            params: vec![Ty::Ptr, Ty::Ptr],
            returns: vec![Ty::Ptr],
            is_vararg: false,
            abi: None,
        })
        .expect("Module::add_func_type: test fixture");
    let addmul = lib
        .functions
        .iter_mut()
        .find(|f| f.name == "addmul")
        .expect("lib.bin defines addmul");
    addmul.ty = boxed;
    let boxed_path = dir.path().join("boxed.bin");
    std::fs::write(
        &boxed_path,
        serialize_module_bytes(&lib).expect("the reboxed lib still has a wire identity"),
    )
    .expect("write boxed.bin");

    let out = dir.path().join("use.bin");
    let err = trustir_bin(&dir.path().join("Use.lean"), "useLib", &out, &[&boxed_path])
        .expect_err("a call shape that disagrees with the far signature must refuse");
    let rendered = format!("{err:#}");
    let expected = LinkRefusal::CallShapeDisagreesWithFarSignature {
        local: "fn(u64, u64) -> (u64)".to_string(),
        far: "fn(ptr, ptr) -> (ptr)".to_string(),
    }
    .to_string();
    assert!(
        rendered.contains("import of `addmul` refused") && rendered.contains(&expected),
        "{rendered}"
    );
    assert!(!out.exists(), "nothing is written");
}

/// A symbol two supplied artifacts define is refused, never resolved by
/// picking one (`SymbolAmbiguous`).
#[test]
fn a_symbol_two_artifacts_define_refuses_the_compile() {
    let dir = project(HONEST_ADDMUL);
    let lib_path = build_lib(dir.path());
    // Same definitions under another module name: a second definer.
    let twin = dir.path().join("twin.bin");
    trustir_bin(&dir.path().join("Lib.lean"), "libRoot", &twin, &[]).expect("twin");
    let out = dir.path().join("use.bin");
    let err = trustir_bin(
        &dir.path().join("Use.lean"),
        "useLib",
        &out,
        &[&lib_path, &twin],
    )
    .expect_err("an ambiguous symbol must refuse");
    assert!(
        format!("{err:#}").contains(&LinkRefusal::SymbolAmbiguous.to_string()),
        "{err:#}"
    );
    assert!(!out.exists(), "nothing is written");
}

/// `--link-artifact` belongs to the linkable artifact only; any other format
/// would drop it silently, so it is refused.
#[test]
fn link_artifact_is_refused_outside_trustir_bin() {
    let dir = project(HONEST_ADDMUL);
    let lib_path = build_lib(dir.path());
    let err = handle_compile_command(CompileArgs {
        file: Some(dir.path().join("Use.lean")),
        decl: Some("useLib".to_owned()),
        emit: EmitFormat::C,
        opt_level: 0,
        output: None,
        link_artifact: vec![lib_path],
    })
    .expect_err("--link-artifact with --emit c must refuse");
    assert!(
        err.to_string()
            .contains("applies only to `--emit trustir-bin`"),
        "{err}"
    );
}

/// The compile ROOT is never imported: an artifact that already defines it
/// would make the output a second definition of the same symbol, so the
/// compile is refused by name and nothing is written.
#[test]
fn a_compile_root_an_artifact_defines_is_refused() {
    let dir = project(HONEST_ADDMUL);
    let lib_path = build_lib(dir.path());
    let out = dir.path().join("again.bin");
    let err = trustir_bin(&dir.path().join("Lib.lean"), "libRoot", &out, &[&lib_path])
        .expect_err("re-defining an artifact's symbol must refuse");
    assert!(
        format!("{err:#}").contains(
            "the compile root `libRoot` (symbol `libRoot`) is defined by a linked artifact"
        ),
        "{err:#}"
    );
    assert!(!out.exists(), "nothing is written");
}

/// `Mid.lean`: a second library that itself imports `Lib`.
const MID_SOURCE: &str = "import Lib\n\
    def midf (a b : UInt64) : UInt64 := addmul a b + a\n";

/// `Top.lean`: a client of BOTH `Mid` and `Lib`.
const TOP_SOURCE: &str = "import Mid\n\
    def top (a b : UInt64) : UInt64 := midf a b + addmul b a\n";

/// REVIEW (legitimate composition wrongly refused): an import CHAIN.
/// `mid.bin` is compiled against `lib.bin`, so it DECLARES `addmul` (its own
/// import of it). A client of both must import `addmul` from the one artifact
/// that DEFINES it and `midf` from `mid.bin`; before the review the
/// declaration counted as a second carrier and the compile was refused as
/// `SymbolAmbiguous`, so no chain longer than one edge could be built (and
/// `mid.bin` alone is not enough: the consumer must authenticate its own
/// import of `lib.bin`).
#[test]
fn a_transitive_import_chain_links_against_both_artifacts() {
    let dir = project(HONEST_ADDMUL);
    std::fs::write(dir.path().join("Mid.lean"), MID_SOURCE).expect("write Mid");
    std::fs::write(dir.path().join("Top.lean"), TOP_SOURCE).expect("write Top");
    let lib_path = build_lib(dir.path());
    let lib = read_module(&lib_path);

    let mid_path = dir.path().join("mid.bin");
    trustir_bin(
        &dir.path().join("Mid.lean"),
        "midf",
        &mid_path,
        &[&lib_path],
    )
    .expect("Mid compiles against lib.bin");
    let mid = read_module(&mid_path);
    assert!(
        named(&mid, "addmul").iter().all(|f| f.is_declaration()),
        "mid.bin imports, never re-defines, addmul"
    );
    assert_eq!(mid.imports.len(), 1);

    let top_path = dir.path().join("top.bin");
    trustir_bin(
        &dir.path().join("Top.lean"),
        "top",
        &top_path,
        &[&lib_path, &mid_path],
    )
    .expect("Top compiles against lib.bin and mid.bin");
    let client = read_module(&top_path);
    for symbol in ["addmul", "midf"] {
        let found = named(&client, symbol);
        assert!(
            found.len() == 1 && found[0].is_declaration(),
            "top.bin must DECLARE, not define, `{symbol}`"
        );
    }
    let mut recorded: Vec<String> = client
        .imports
        .iter()
        .map(|i| i.digest.to_string())
        .collect();
    recorded.sort();
    let mut expected = vec![digest(&lib), digest(&mid)];
    expected.sort();
    assert_eq!(recorded, expected, "one row per artifact the client uses");
    let verdict = linked_verdict(&client, &[lib, mid]);
    assert!(verdict.is_empty(), "{verdict:?}");
}

/// REVIEW (legitimate build wrongly refused): the same artifact named twice
/// is ONE definer of each of its symbols — identity is the digest, never the
/// path — so it is not `SymbolAmbiguous`, and it is one import row.
#[test]
fn the_same_artifact_named_twice_is_one_definer() {
    let dir = project(HONEST_ADDMUL);
    let lib_path = build_lib(dir.path());
    let copy = dir.path().join("copy.bin");
    std::fs::copy(&lib_path, &copy).expect("copy lib.bin");
    let use_path = dir.path().join("use.bin");
    trustir_bin(
        &dir.path().join("Use.lean"),
        "useLib",
        &use_path,
        &[&lib_path, &copy, &lib_path],
    )
    .expect("one module named three times links once");
    let client = read_module(&use_path);
    assert_eq!(client.imports.len(), 1);
    let lib = read_module(&lib_path);
    assert_eq!(client.imports[0].digest.to_string(), digest(&lib));
    assert!(linked_verdict(&client, std::slice::from_ref(&lib)).is_empty());
}
