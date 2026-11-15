// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! One Lean module name per file, in every driver (G21 brick B4,
//! `designs/2026-10-08-private-name-mangling.md`): a `private` declaration is
//! `_private.<Module>.0.<name>` whether the file is checked by `clean project
//! check`, by `clean check` through an import, or by `clean check` on its
//! absolute path. Every expectation was measured on pinned Lean 4.8.0
//! (`lake build`, 2026-10-09).

use super::*;

const LAKEFILE: &str = "import Lake\nopen Lake DSL\npackage pkg where\n\
                        @[default_target]\nlean_lib Pkg where\n  srcDir := \".\"\n";
const SIBLING_A: &str = "private theorem helper : True := True.intro\n\
                         theorem a_ok : True := helper\n";
const SIBLING_B: &str = "private theorem helper : True := True.intro\n\
                         theorem b_ok : True := helper\n";

/// The G21 shape under `clean project check`: two siblings each declare
/// `private theorem helper`, and an importer of both checks (Lean builds it).
/// The twin, an importer naming `helper`, is refused (Lean: `unknown
/// identifier 'helper'`).
#[test]
fn test_project_check_private_siblings_check_and_stay_module_local() {
    for (label, importer, passes) in [
        (
            "importer",
            "import Pkg.A\nimport Pkg.B\ntheorem c_ok : True := a_ok\ntheorem c_ok2 : True := b_ok\n",
            true,
        ),
        (
            "twin",
            "import Pkg.A\nimport Pkg.B\ntheorem g21_twin : True := helper\n",
            false,
        ),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        write_project(
            dir.path(),
            &[
                ("lakefile.lean", LAKEFILE),
                ("Pkg/A.lean", SIBLING_A),
                ("Pkg/B.lean", SIBLING_B),
                ("Pkg/C.lean", importer),
            ],
        );
        let (output, report) = check_project(dir.path());
        let c = module_report(&report, "Pkg.C");
        assert!(
            blocker_messages(&report, "import_environment_divergence").is_empty(),
            "{label}: {report}"
        );
        if passes {
            assert!(output.status.success(), "{label}: {report}");
            assert_eq!(c["status"], "pass", "{label}: {report}");
            assert_eq!(usize_field(c, "success_count"), 2, "{label}: {report}");
        } else {
            assert!(!output.status.success(), "{label}: {report}");
            assert_eq!(c["status"], "fail", "{label}: {report}");
            assert_eq!(usize_field(c, "success_count"), 0, "{label}: {report}");
        }
    }
}

/// An entry file invoked by its ABSOLUTE path gets Lake's module name, so
/// its private axiom is `_private.Pkg.P.0.ax`, the text Lean 4.8.0's
/// `#print axioms` prints. Before B4 the name was derived from the absolute
/// path (`_private.private.var.….Pkg.P.0.ax`) and the `#guard_msgs` failed;
/// the relative invocation from the package root always passed.
#[test]
fn test_clean_check_absolute_entry_gets_the_lake_module_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("lakefile.lean", LAKEFILE),
            (
                "Pkg/P.lean",
                "private axiom ax : True\ntheorem uses : True := ax\n\
                 /-- info: 'uses' depends on axioms: [_private.Pkg.P.0.ax] -/\n\
                 #guard_msgs in\n#print axioms uses\n",
            ),
        ],
    );
    let (output, report) = clean_check_json(&dir.path().join("Pkg/P.lean"));
    assert!(output.status.success(), "{report}");
    assert_eq!(report["errors"], serde_json::json!([]), "{report}");
    assert_eq!(usize_field(&report, "success_count"), 3, "{report}");
}

/// G14 under `clean check`: an imported module's failure is tagged with the
/// name the `import` wrote (`[Pkg.A]`), as Lean's `lake build` names the
/// failing module, never with a name derived from its absolute path.
#[test]
fn test_clean_check_tags_an_imported_failure_with_its_module_name() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("lakefile.lean", LAKEFILE),
            (
                "Pkg/A.lean",
                "def bad : Nat := \"x\"\ndef good : Nat := 1\n",
            ),
            ("Pkg/B.lean", "import Pkg.A\ndef user : Nat := good\n"),
        ],
    );
    let (output, report) = clean_check_json(&dir.path().join("Pkg/B.lean"));
    assert!(!output.status.success(), "{report}");
    let errors: Vec<&str> = report["errors"]
        .as_array()
        .expect("errors")
        .iter()
        .filter_map(|e| e.as_str())
        .collect();
    assert!(
        errors.iter().any(|e| e.starts_with("[Pkg.A] bad: ")),
        "{errors:#?}"
    );
    assert!(
        errors.iter().all(|e| !e.contains(".Pkg.A]")),
        "no path-derived tag: {errors:#?}"
    );
}

/// Two files never share a module name, so never a `_private.<M>.0` prefix
/// (G21 review, probe `rv/srcdir`). With `srcDir := "src"`, the entry
/// `src/A.lean` is `A`; `src/sub/B.lean`'s `import A` used to resolve by the
/// parent-directory fallback to `src/sub/A.lean` and name THAT file `A` too,
/// so the entry's private step reached the other file's private theorems and
/// the entry's own `private theorem helper` was refused as already declared.
/// Pinned Lean 4.8.0 `lake build` refuses this layout ("build cycle
/// detected"); `clean check` now refuses it by name. The control imports
/// `sub.A` by its own name and checks.
#[test]
fn test_clean_check_refuses_two_files_with_one_module_name() {
    const SRC_LAKEFILE: &str = "import Lake\nopen Lake DSL\npackage p where\n\
                                @[default_target]\nlean_lib A where\n  srcDir := \"src\"\n\
                                  globs := #[.one `A, .submodules `sub]\n";
    const SUB_A: &str = "private theorem helper : True := True.intro\n\
                         theorem a_ok : True := helper\n";
    const ENTRY: &str = "import sub.B\nprivate theorem helper : True := True.intro\n\
                         theorem t : True := helper\n";
    for (label, sub_b, passes) in [
        (
            "collision",
            "import A\ntheorem b : True := True.intro\n",
            false,
        ),
        ("control", "import sub.A\ntheorem b : True := a_ok\n", true),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        write_project(
            dir.path(),
            &[
                ("lakefile.lean", SRC_LAKEFILE),
                ("src/A.lean", ENTRY),
                ("src/sub/B.lean", sub_b),
                ("src/sub/A.lean", SUB_A),
            ],
        );
        let output = run_clean(&[
            "check",
            dir.path().join("src/A.lean").to_str().expect("utf8"),
        ]);
        let text = format!(
            "{}{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        if passes {
            assert!(output.status.success(), "{label}: {text}");
        } else {
            assert!(!output.status.success(), "{label}: {text}");
            assert!(
                text.contains("module name `A` would name two files"),
                "{label}: {text}"
            );
        }
    }
}
