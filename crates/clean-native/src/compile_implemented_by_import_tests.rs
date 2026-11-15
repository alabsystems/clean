// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `@[implemented_by]` and `@[extern]` bindings an IMPORTED module carries,
//! through the production `clean run` emit + link path, over a `.olean` the
//! pinned Lean v4.30.0-rc2 compiles (fixture family `implemented_by_import`,
//! `crates/clean-olean/tests/fixtures/lean/v4.30.0-rc2/implemented_by_import/`,
//! and the families `implemented_by_late` and `implemented_by_shadowed`
//! beside it).
//!
//! Before `docs/DECISIONS.md` R149 the loader registered neither attribute,
//! so the imported declaration's logical body compiled: `implSlow 1` printed
//! `3`, `implCaller 1` `30`, `chainHead 1` `10`, `unsafeSlow 1` `201` and
//! `externBody 1` `4`, each at exit 0, where pinned Lean prints `2`, `20`,
//! `8` and `101` and fails `externBody` ("Could not find native
//! implementation of external declaration 'externBody'", exit 1). Every
//! expected output below is what `lean --run` printed for the same program.

use std::path::{Path, PathBuf};
use std::process::Command;

use super::implemented_by_tests::mentions_symbol;
use crate::native_build::{build_native_binary_in_scratch, emit_entry_c_with_type};

/// A Lake-shaped project whose build directory holds the fixture's `.olean`
/// (the layout `clean run` finds a dependency's artifacts in), with `Main.lean`
/// importing it and printing `expr`.
fn project(expr: &str) -> (tempfile::TempDir, PathBuf) {
    project_of("implemented_by_import", "ImplByLib", expr)
}

/// [`project`] over module `module` of fixture family `family`.
fn project_of(family: &str, module: &str, expr: &str) -> (tempfile::TempDir, PathBuf) {
    let fixture = clean_olean::test_support::compiled_fixture_dir(family);
    let dir = tempfile::tempdir().expect("tempdir");
    std::fs::write(dir.path().join("lakefile.toml"), "").expect("write lakefile");
    let lib = dir.path().join(".lake/build/lib/lean");
    std::fs::create_dir_all(&lib).expect("create build dir");
    let olean = format!("{module}.olean");
    std::fs::copy(fixture.join(&olean), lib.join(&olean)).expect("copy the fixture .olean");
    let file = dir.path().join("Main.lean");
    std::fs::write(
        &file,
        format!("import {module}\n\ndef main : IO Unit := IO.println (toString ({expr}))\n"),
    )
    .expect("write Main.lean");
    (dir, file)
}

/// FAIL-CLOSED on a missing C compiler, with no skip path: these tests
/// assert the bytes a linked program prints.
fn require_cc() {
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let has_cc = Command::new(&cc)
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success());
    assert!(
        has_cc,
        "a C compiler (`{cc}`) is required: these tests assert the bytes a linked program prints"
    );
}

/// Emit, link and run `main` of `file`: (emitted C, stdout, exit status).
fn build_and_run(file: &Path) -> (String, String, i32) {
    require_cc();
    let (emitted, ty) = emit_entry_c_with_type(file, "main", 0)
        .unwrap_or_else(|e| panic!("`main` must compile: {e:#}"));
    let built =
        build_native_binary_in_scratch("main", &emitted, ty.as_ref(), true).expect("link main");
    let output = Command::new(&built.binary).output().expect("run main");
    (
        emitted,
        String::from_utf8_lossy(&output.stdout).into_owned(),
        output.status.code().unwrap_or(-1),
    )
}

/// The refusal `clean run` reports for `main` of `file`.
fn refusal(file: &Path) -> String {
    match emit_entry_c_with_type(file, "main", 0) {
        Ok((c, _)) => panic!("the native path COMPILED `main`; it must refuse:\n{c}"),
        Err(err) => format!("{err:#}"),
    }
}

/// An imported `@[implemented_by]` runs its implementation, directly, from
/// an imported caller, and at the END of an imported chain; none of the
/// rebound bodies is compiled.
#[test]
fn test_imported_implemented_by_runs_the_implementation() {
    for (expr, lean_prints, never) in [
        ("implSlow 1", "2\n", "l_implSlow"),
        ("implCaller 1", "20\n", "l_implSlow"),
        ("chainHead 1", "8\n", "l_chainMid"),
    ] {
        let (_dir, file) = project(expr);
        let (c, stdout, status) = build_and_run(&file);
        assert_eq!(
            (stdout.as_str(), status),
            (lean_prints, 0),
            "`{expr}`: pinned Lean prints {lean_prints:?} at exit 0"
        );
        assert!(
            !mentions_symbol(&c, never),
            "`{expr}`: `{never}` is never compiled:\n{c}"
        );
    }
}

/// An imported `@[implemented_by]` whose implementation is `unsafe` is
/// refused by name: Lean runs the unsafe body (`101`), Clean compiles no
/// unsafe code, and the logical body (`201`) must not run in its place.
#[test]
fn test_imported_unsafe_implementation_refused_by_name() {
    let (_dir, file) = project("unsafeSlow 1");
    let msg = refusal(&file);
    assert!(
        msg.contains("unsafeSlow") && msg.contains("unsafeFast") && msg.contains("`unsafe`"),
        "{msg}"
    );
    assert!(msg.contains("(implemented-by)"), "{msg}");
}

/// An imported `@[extern]` declaration with a body is refused by name, as a
/// source one is: Lean calls its symbol and never the body (`4`).
#[test]
fn test_imported_extern_with_body_refused_by_name() {
    let (_dir, file) = project("externBody 1");
    let msg = refusal(&file);
    assert!(msg.contains("(native-extern-body)"), "{msg}");
    assert!(
        msg.contains("externBody") && msg.contains("clean_implby_fixture_no_such_symbol"),
        "{msg}"
    );
}

/// Control: an imported declaration with no attribute compiles its body.
#[test]
fn test_imported_plain_declaration_compiles_its_body() {
    let (_dir, file) = project("plainLib 1");
    let (_c, stdout, status) = build_and_run(&file);
    assert_eq!((stdout.as_str(), status), ("6\n", 0));
}

/// A LATE binding in a Lean-built module (fixture family
/// `implemented_by_late`): `attribute [implemented_by lateFast] lateSlow`
/// after `lateCaller`. Pinned Lean prints `30` for `lateCaller 1` (the caller
/// was compiled before the binding) and `20` for `lateAfter 1`; before the
/// loader judged the binding, both printed `20` at exit 0. Every root is
/// refused, naming the caller and the declaration's own code.
#[test]
fn test_imported_late_binding_refuses_every_root() {
    for expr in ["lateCaller 1", "lateAfter 1", "lateFast 1"] {
        let (_dir, file) = project_of("implemented_by_late", "LateLib", expr);
        let msg = refusal(&file);
        assert!(
            msg.contains("(native-implemented-by-order)"),
            "`{expr}`: {msg}"
        );
        assert!(
            msg.contains("`lateCaller` names `lateSlow`")
                && msg.contains("`lateSlow` itself was compiled before the binding"),
            "`{expr}`: {msg}"
        );
    }
}

/// A late binding of an `@[inline]` declaration: Lean prints `30` for
/// `inlineCaller 1` and `3` for `inlineSlow 1` (the pre-binding body is
/// inlined into the importer); both refused.
#[test]
fn test_imported_late_inline_binding_refused() {
    for expr in ["inlineCaller 1", "inlineSlow 1"] {
        let (_dir, file) = project_of("implemented_by_late", "LateInline", expr);
        let msg = refusal(&file);
        assert!(
            msg.contains("(native-implemented-by-order)"),
            "`{expr}`: {msg}"
        );
        assert!(msg.contains("`inlineSlow`"), "`{expr}`: {msg}");
    }
}

/// A `@[macro_inline]` declaration's binding: Lean expands the body at every
/// call site, so `macroCaller 1` prints `30` and `macroSlow 1` prints `3`;
/// the loader registers no binding and the body compiles.
#[test]
fn test_imported_macro_inline_binding_runs_the_body() {
    for (expr, lean_prints) in [("macroCaller 1", "30\n"), ("macroSlow 1", "3\n")] {
        let (_dir, file) = project_of("implemented_by_late", "LateMacro", expr);
        let (c, stdout, status) = build_and_run(&file);
        assert_eq!(
            (stdout.as_str(), status),
            (lean_prints, 0),
            "`{expr}`: pinned Lean prints {lean_prints:?} at exit 0"
        );
        assert!(!mentions_symbol(&c, "l_macroFast"), "`{expr}`:\n{c}");
    }
}

/// Bindings that are not late print Lean's bytes: a recursive declaration
/// bound on itself (its compiled recursion calls `recFast`), through a caller
/// and directly, a late binding of a `@[noinline]` declaration nothing in
/// the module reaches, and a binding written on its declaration inside a
/// macro, whose hygienic name ends in a number (`LateHyg`; while the
/// judgement read such a name as compiled structurally, every program that
/// imports `Std` was refused for the order hazard), and an axiom bound on its
/// declaration (`LateAx`; read as compiled structurally, it refused every
/// program that imports `Lean`).
#[test]
fn test_imported_bindings_that_are_not_late_run_the_implementation() {
    for (module, expr, lean_prints) in [
        ("LateOk", "recCaller 3", "90\n"),
        ("LateOk", "recSlow 3", "9\n"),
        ("LateOk", "okSlow 1", "2\n"),
        ("LateHyg", "hygCaller 1", "20\n"),
        ("LateHyg", "hygFast 1", "2\n"),
        ("LateAx", "axCaller 1", "20\n"),
        ("LateAx", "axFast 1", "2\n"),
    ] {
        let (_dir, file) = project_of("implemented_by_late", module, expr);
        let (_c, stdout, status) = build_and_run(&file);
        assert_eq!(
            (stdout.as_str(), status),
            (lean_prints, 0),
            "`{expr}`: pinned Lean prints {lean_prints:?} at exit 0"
        );
    }
}

/// Constructors bound by the command form (`LateCtor`): Lean never runs
/// such a binding (`ctorUse 1`, `tUse 1` print `1`, `(pf 1).a` prints
/// `11`), so every root is refused, an over-refusal. Registered as an
/// on-declaration binding, `clean run` of each exited 139 (a SIGSEGV).
#[test]
fn test_imported_constructor_binding_refuses_every_root() {
    for (expr, rebound) in [
        ("ctorUse 1", "`P.mk`"),
        ("tUse 1", "`T.leaf`"),
        ("(pf 1).a", "`P.mk`"),
    ] {
        let (_dir, file) = project_of("implemented_by_late", "LateCtor", expr);
        let msg = refusal(&file);
        assert!(
            msg.contains("(native-implemented-by-order)"),
            "`{expr}`: {msg}"
        );
        assert!(msg.contains(rebound), "`{expr}`: {msg}");
    }
}

/// The text of the refusal `link_types_agree` names a link by.
fn type_mismatch_refusal(decl: &str, target: &str) -> String {
    format!(
        "`{decl}` is @[implemented_by {target}], and in this environment `{target}` \
         does not have the type of `{decl}`"
    )
}

/// An imported binding whose target Clean's builtin prelude types otherwise
/// (fixture family `implemented_by_shadowed`, a Lean-written `.olean`) is
/// followed in the declarations Lean held. The artifact has no Clean
/// payload, so the program environment is the selected world's genuine Init
/// (`source_closure_needs_world_setup`, `docs/DECISIONS.md`), not the builtin
/// prelude; neither target is a resident of another type there. Pinned
/// v4.30.0-rc2 Lean accepted both bindings against its own declarations:
///
/// * `modVia` is `@[implemented_by Nat.modCore]`, which genuine Init types
///   `Nat → Nat → Nat` and declares `@[extern "lean_nat_mod"]` with a body
///   (`Init/Prelude.lean`). Lean's own build of `modVia 7 3` fails ("Failed
///   to find LCNF signature for Nat.modCore", exit 1). The link is followed
///   and the native path refuses its END by name (`native-extern-body`), as
///   it refuses any extern with a body; it never compiles that body, and it
///   never calls a three-place function with two arguments, as following the
///   builtin prelude's fuelled `Nat.modCore` would.
/// * `finEqVia` is `@[implemented_by instDecidableEqFin]`, which Lean types
///   `(n : Nat) → DecidableEq (Fin n)`, as genuine Init does. Lean prints
///   `true` for `finSelfEq ()`. Over the builtin prelude, which holds that
///   instance unfolded, this was an over-refusal pinned to fail loudly the
///   day it closed; genuine Init closed it.
///
/// The type check itself stays where the link is followed, for a binding
/// whose target the environment types otherwise
/// (`clean_compiler::implemented_by_tests::test_runtime_const_name_names_a_type_mismatch`).
#[test]
fn test_imported_binding_to_a_shadowed_resident_follows_genuine_init() {
    let (_dir, file) = project_of("implemented_by_shadowed", "ShadowLib", "modVia 7 3");
    let msg = refusal(&file);
    assert!(
        msg.contains("native build refuses `Nat.modCore` (reached from `main`)")
            && msg.contains("@[extern \"lean_nat_mod\"] with a body")
            && msg.contains("(native-extern-body)"),
        "`modVia 7 3`: the link to genuine `Nat.modCore` is followed and its end refused \
         by name: {msg}"
    );
    assert!(
        !msg.contains(&type_mismatch_refusal("modVia", "Nat.modCore")),
        "`modVia 7 3`: genuine `Nat.modCore` has the type of `modVia`: {msg}"
    );

    let (_dir, file) = project_of("implemented_by_shadowed", "ShadowLib", "finSelfEq ()");
    let (c, stdout, status) = build_and_run(&file);
    assert_eq!(
        (stdout.as_str(), status),
        ("true\n", 0),
        "`finSelfEq ()`: pinned Lean prints \"true\" at exit 0"
    );
    assert!(
        !mentions_symbol(&c, "l_finEqVia"),
        "`finEqVia`'s logical body is never compiled:\n{c}"
    );
}
