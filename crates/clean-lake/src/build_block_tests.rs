// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `clean lake build` over `namespace` / `section` blocks and `example`s.
//!
//! Measured on `317f48b45` and on clean `main` (round-22 verification): a
//! module whose `section` held `theorem bad : 1 = 2 := rfl` printed `Build OK`,
//! exited 0 and wrote its `.olean`, because the builder's own commit step
//! answered `Ok(())` for a block (`Multiple`) and for its `Failed` members. The
//! same arm dropped every GOOD member of a multi-declaration block, so a
//! sibling citing an earlier sibling failed with `Unknown identifier`. An
//! `example` was never gated at all: `example : 1 = 2 := sorry` built.

use super::*;
use tempfile::TempDir;

/// A two-module package: `MyProject.Core` holds `core`, `MyProject.Main`
/// imports it and holds `main`.
fn project(core: &str, main: &str) -> TempDir {
    let tmp = TempDir::new().expect("tempdir");
    std::fs::write(
        tmp.path().join("lakefile.lean"),
        "package myproject\n\nlean_lib MyProject where\n  roots := #[`MyProject]\n",
    )
    .expect("write lakefile");
    std::fs::create_dir_all(tmp.path().join("MyProject")).expect("create src dir");
    std::fs::write(tmp.path().join("MyProject/Core.lean"), core).expect("write Core");
    std::fs::write(
        tmp.path().join("MyProject/Main.lean"),
        format!("import MyProject.Core\n{main}"),
    )
    .expect("write Main");
    tmp
}

fn build(tmp: &TempDir, check_only: bool) -> BuildResult {
    let ws = Workspace::load(tmp.path()).expect("workspace loads");
    BuildContext::new(ws)
        .with_options(BuildOptions {
            check_only,
            ..Default::default()
        })
        .build_all()
        .expect("build runs")
}

fn core_olean(tmp: &TempDir) -> std::path::PathBuf {
    tmp.path().join(".lake/build/lib/MyProject/Core.olean")
}

/// Every shape that used to build: each must now refuse `MyProject.Core`, in
/// both the ordinary and the check-only build, and write no artifact.
#[test]
fn a_failing_declaration_anywhere_in_a_module_refuses_the_module() {
    let attacks: &[(&str, &str)] = &[
        ("section, bad only", "section S\ntheorem bad : 1 = 2 := rfl\nend S\n"),
        (
            "section, good then bad",
            "section S\ntheorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := rfl\nend S\n",
        ),
        (
            "namespace > namespace > section",
            "namespace A\nnamespace B\nsection S\ntheorem bad : 1 = 2 := rfl\nend S\nend B\nend A\n",
        ),
        (
            "namespace, good then bad",
            "namespace A\ntheorem good : 1 = 1 := rfl\ntheorem bad : 1 = 2 := rfl\nend A\n",
        ),
        ("false example in a section", "section S\nexample : 1 = 2 := rfl\nend S\n"),
        ("sorry example", "example : 1 = 2 := sorry\n"),
        ("sorry example in a namespace", "namespace A\nexample : 1 = 2 := sorry\nend A\n"),
        (
            "sorry codef in a section",
            "section X\ncodata Strm (A : Type) where\n  head : A\n  tail : Strm A\n\n\
             codef natsFrom (n : Nat) : Strm Nat where\n  head := sorry\n  \
             tail := natsFrom (Nat.succ n)\nend X\n",
        ),
        (
            "failed mutual sibling in a namespace",
            "namespace A\nmutual\ndef ev : Nat -> Bool\n  | 0 => true\n  | n+1 => od n\n\
             def od : Nat -> Bool\n  | 0 => false\n  | n+1 => ev n\nend\n\
             theorem bad : ev 2 = false := rfl\nend A\n",
        ),
    ];
    for (label, core) in attacks {
        for check_only in [false, true] {
            let tmp = project(core, "def mainVal : Nat := 0\n");
            let result = build(&tmp, check_only);
            assert!(
                result.failed.iter().any(|(m, _)| m == "MyProject.Core"),
                "{label} (check_only={check_only}): Core must fail, got {result:?}"
            );
            assert!(
                !result.built.iter().any(|m| m == "MyProject.Core"),
                "{label} (check_only={check_only}): Core must not be built"
            );
            assert!(
                !core_olean(&tmp).exists(),
                "{label} (check_only={check_only}): no artifact for a refused module"
            );
        }
    }
}

/// The other half of the same defect: good block members must reach the
/// environment (so siblings can cite them) and the artifact (so an importer
/// can).
#[test]
fn block_members_reach_their_siblings_and_the_artifact() {
    let core = "namespace A\ntheorem g1 : 1 = 1 := rfl\ntheorem g2 : 1 = 1 := g1\nend A\n\
                section S\ndef d1 : Nat := 1\ndef d2 : Nat := d1 + 1\nend S\n\
                namespace B\nstructure P where\n  x : Nat\n  y : Nat\n\
                def p : P := { x := 1, y := 2 }\nend B\n\
                example : A.g2 = A.g2 := rfl\n";
    let main = "theorem u1 : 1 = 1 := A.g2\ntheorem u2 : d2 = 2 := rfl\n\
                theorem u3 : B.p.y = 2 := rfl\n";
    let tmp = project(core, main);
    let result = build(&tmp, false);
    assert!(
        result.failed.is_empty(),
        "a valid package must build: {result:?}"
    );
    assert!(core_olean(&tmp).exists(), "Core's artifact must be written");

    // And an importer's false claim about a block member is still refused.
    let tmp = project(core, "namespace Z\ntheorem bad : 1 = 2 := A.g1\nend Z\n");
    let result = build(&tmp, false);
    assert!(
        result.failed.iter().any(|(m, _)| m == "MyProject.Main"),
        "Main's failing namespaced theorem must refuse Main: {result:?}"
    );
}
