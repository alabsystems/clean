// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! A module sees exactly what it imports: nothing from a sibling it does
//! not import, and the instances Lean gives it.

use super::*;

// ─────────────────────────────────────────────────────────────────────────────
// Per-module import environments (round-24 verification of af6ae8e4a).
// `project check` used to check every module against ONE environment in load
// order, so a module saw declarations and instances of modules it does not
// import. Each case below was accepted (or wrongly refused) that way; Lean
// 4.8.0 gives the verdict each assertion states.
// ─────────────────────────────────────────────────────────────────────────────

const OFNAT_TWO_IS_THREE: &str = "instance (priority := high) three : OfNat Nat 2 := ⟨3⟩\n\
                                  theorem a_ok : (1 : Nat) = 1 := rfl\n";

/// B imports nothing, so `(2 : Nat) = 3` is false as written; A's instance
/// must not reach it (Lean: type mismatch). Also with an unrelated import.
#[test]
fn an_instance_in_a_module_not_imported_does_not_reach_a_module() {
    for (label, importer) in [
        ("no import", "theorem t : (2 : Nat) = 3 := rfl\n"),
        (
            "unrelated import",
            "import Other\ntheorem t : (2 : Nat) = 3 := rfl\n",
        ),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        write_project(
            dir.path(),
            &[
                ("A.lean", OFNAT_TWO_IS_THREE),
                ("Other.lean", "theorem o : (0 : Nat) = 0 := rfl\n"),
                ("B.lean", importer),
            ],
        );
        let (output, report) = check_project(dir.path());
        assert!(!output.status.success(), "{label}: {report}");
        let b = module_report(&report, "B");
        assert_eq!(b["status"], "fail", "{label}: {report}");
        assert_eq!(usize_field(b, "success_count"), 0, "{label}: {report}");
        let (check_output, check_report) = clean_check_json(&dir.path().join("B.lean"));
        assert!(!check_output.status.success(), "{label}: {check_report}");
    }
}

/// B cites A's theorem without importing A: an unknown identifier in Lean.
#[test]
fn a_declaration_in_a_module_not_imported_cannot_be_cited() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("A.lean", "theorem a : (1 : Nat) = 1 := rfl\n"),
            ("B.lean", "theorem b : (1 : Nat) = 1 := a\n"),
        ],
    );
    let (output, report) = check_project(dir.path());
    assert!(!output.status.success(), "{report}");
    assert_eq!(module_report(&report, "B")["status"], "fail", "{report}");
    assert_eq!(usize_field(module_report(&report, "B"), "success_count"), 0);
}

/// The leak in the other direction: a sorry instance in A must not fail a
/// valid B that does not import A.
#[test]
fn a_module_not_imported_cannot_fail_a_valid_module() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            (
                "A.lean",
                "instance (priority := high) bad : OfNat Nat 2 := sorry\n",
            ),
            ("B.lean", "theorem t : (2 : Nat) = 2 := rfl\n"),
        ],
    );
    let (output, report) = check_project(dir.path());
    assert!(!output.status.success(), "{report}");
    assert_eq!(module_report(&report, "A")["status"], "fail", "{report}");
    let b = module_report(&report, "B");
    assert_eq!(b["status"], "pass", "{report}");
    assert_eq!(usize_field(b, "success_count"), 1, "{report}");
}

/// Main imports A and B, which do not import each other. In Lean `two` is
/// B's `2` (B was compiled without A), so `two = 3` is false; elaborated next
/// to A's instance, `two` became 3 and Main's theorem was credited. Every
/// import order and seed choice must refuse it without crediting it.
#[test]
fn a_sibling_import_does_not_change_what_an_import_defines() {
    for (label, extra, main) in [
        (
            "A first",
            None,
            "import A\nimport B\ntheorem m : two = 3 := rfl\n",
        ),
        (
            "B first",
            None,
            "import B\nimport A\ntheorem m : two = 3 := rfl\n",
        ),
        (
            "A is the larger closure",
            Some(("Base.lean", "theorem base_ok : (0 : Nat) = 0 := rfl\n")),
            "import A\nimport B\ntheorem m : two = 3 := rfl\n",
        ),
        (
            "through a function",
            None,
            "import A\nimport B\ntheorem m : f 0 = 3 := rfl\n",
        ),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let a = if extra.is_some() {
            format!("import Base\n{OFNAT_TWO_IS_THREE}")
        } else {
            OFNAT_TWO_IS_THREE.to_string()
        };
        let mut files = vec![
            ("A.lean", a.as_str()),
            (
                "B.lean",
                "def two : Nat := 2\ndef f (n : Nat) : Nat := n + 2\n\
                 theorem b_ok : two = two := rfl\n",
            ),
            ("Main.lean", main),
        ];
        files.extend(extra);
        write_project(dir.path(), &files);
        let (output, report) = check_project(dir.path());
        assert!(!output.status.success(), "{label}: {report}");
        let entry = module_report(&report, "Main");
        assert_eq!(entry["status"], "fail", "{label}: {report}");
        assert_eq!(usize_field(entry, "success_count"), 0, "{label}: {report}");
        for module in ["A", "B"] {
            assert_eq!(
                module_report(&report, module)["status"],
                "pass",
                "{label}: {report}"
            );
        }
        // `clean check Main.lean` elaborated A and B into one environment and
        // credited `m` (round-24 verification of 2bcef9307).
        let (check_output, check_report) = clean_check_json(&dir.path().join("Main.lean"));
        assert!(!check_output.status.success(), "{label}: {check_report}");
        assert_eq!(
            usize_field(&check_report, "success_count"),
            0,
            "{label}: {check_report}"
        );
    }
}

/// Controls: what an import DOES bring is still visible — an instance
/// reached through an import, and a diamond — so the fix is not a refusal
/// of every multi-import module. Lean accepts all of these.
#[test]
fn what_a_module_imports_is_still_visible() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            (
                "C.lean",
                "instance (priority := high) three : OfNat Nat 2 := ⟨3⟩\n\
                 theorem c_ok : (2 : Nat) = 3 := rfl\n",
            ),
            ("B.lean", "theorem b_ok : (1 : Nat) = 1 := rfl\n"),
            (
                "D.lean",
                "import B\nimport C\ntheorem d : (2 : Nat) = 3 := rfl\n",
            ),
            (
                "One.lean",
                "def one : Nat := 1\ntheorem one_eq : one = 1 := rfl\n",
            ),
            ("L.lean", "import One\ntheorem l : one + one = 2 := rfl\n"),
            ("R.lean", "import One\ntheorem r : one * 3 = 3 := rfl\n"),
            (
                "Top.lean",
                "import L\nimport R\ntheorem t1 : one + 1 = 2 := rfl\n\
                 theorem t2 : one = 1 := one_eq\n",
            ),
        ],
    );
    let (output, report) = check_project(dir.path());
    assert!(output.status.success(), "{report}");
    for module in ["B", "C", "D", "One", "L", "R", "Top"] {
        assert_eq!(
            module_report(&report, module)["status"],
            "pass",
            "{module}: {report}"
        );
    }
    assert_eq!(usize_field(&report["summary"], "declarations_passed"), 10);
    // `clean check` accepts every one of them too, sibling imports included.
    for module in ["D", "Top"] {
        let (check_output, check_report) =
            clean_check_json(&dir.path().join(format!("{module}.lean")));
        assert!(check_output.status.success(), "{module}: {check_report}");
    }
}

/// A module refused for `import_environment_divergence` is not checked, and
/// the environment built for it holds the leaked re-elaboration (`two := 3`).
/// It used to be kept as a snapshot anyway, so a module importing it was
/// seeded from it and `theorem m : two = 3 := rfl` was credited (1/1, in
/// `declarations_passed`; M3 2/2 through `m`) although Lean 4.8.0 rejects
/// both M2 and M3 (round-24 verification of 2bcef9307). Every module that
/// reaches the refused one must be refused unchecked, crediting nothing.
#[test]
fn a_module_refused_for_divergence_does_not_seed_its_importers() {
    for (label, x_body, with_m3) in [
        (
            "X with a theorem",
            "theorem x : True := True.intro\n",
            false,
        ),
        ("X import-only", "", false),
        ("two levels", "theorem x : True := True.intro\n", true),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let x = format!("import P\nimport Q\n{x_body}");
        let mut files = vec![
            (
                "P.lean",
                "instance (priority := high) three : OfNat Nat 2 := ⟨3⟩\n".to_string(),
            ),
            ("Q.lean", "def two : Nat := 2\n".to_string()),
            ("X.lean", x),
            (
                "M2.lean",
                "import X\ntheorem m : two = 3 := rfl\n".to_string(),
            ),
        ];
        if with_m3 {
            files.push((
                "M3.lean",
                "import M2\ntheorem m3 : two = 3 := m\ntheorem m3' : two = 3 := rfl\n".to_string(),
            ));
        }
        let borrowed = files
            .iter()
            .map(|(name, text)| (*name, text.as_str()))
            .collect::<Vec<_>>();
        write_project(dir.path(), &borrowed);
        let (output, report) = check_project(dir.path());
        assert!(!output.status.success(), "{label}: {report}");
        let x_report = module_report(&report, "X");
        assert_eq!(x_report["status"], "fail", "{label}: {report}");
        assert!(
            !blocker_messages(&report, "import_environment_divergence").is_empty(),
            "{label}: {report}"
        );
        let mut refused = vec!["M2"];
        if with_m3 {
            refused.push("M3");
        }
        for module in refused {
            let entry = module_report(&report, module);
            assert_eq!(
                entry["status"], "import_failed",
                "{label} {module}: {report}"
            );
            assert_eq!(entry["checked"], false, "{label} {module}: {report}");
            assert_eq!(
                usize_field(entry, "success_count"),
                0,
                "{label} {module}: {report}"
            );
            assert_eq!(
                usize_field(entry, "checked_count"),
                0,
                "{label} {module}: {report}"
            );
            assert!(
                entry["diagnostics"]
                    .as_array()
                    .expect("diagnostics")
                    .iter()
                    .any(|d| d["kind"] == "import_not_loaded"),
                "{label} {module} must say why it was not checked: {report}"
            );
        }
        // `clean check` refuses them too: it elaborated P and Q into one
        // environment, and credited `m` (and M3's two) with `two := 3`.
        let mut entries = vec!["M2"];
        if with_m3 {
            entries.push("M3");
        }
        for module in entries {
            let (check_output, check_report) =
                clean_check_json(&dir.path().join(format!("{module}.lean")));
            assert!(
                !check_output.status.success(),
                "{label} {module}: {check_report}"
            );
            assert_eq!(
                usize_field(&check_report, "success_count"),
                0,
                "{label} {module}: {check_report}"
            );
            assert!(
                check_report
                    .to_string()
                    .contains("import_environment_divergence"),
                "{label} {module}: {check_report}"
            );
        }
        // Only P's and Q's own declarations (and X's `x`, never credited
        // because X is refused) exist; nothing that says `two = 3` is passed.
        assert_eq!(
            usize_field(&report["summary"], "declarations_passed"),
            2,
            "{label}: {report}"
        );
    }
}

/// A module whose import was never loaded — it could not be read or parsed,
/// or it sits in an import cycle — is not checked against an environment
/// missing that import. It used to be (`import_failed`, 1/1, counted in
/// `declarations_passed`), and could then be credited with a meaning the
/// missing import changes.
#[test]
fn a_module_whose_import_was_not_loaded_is_not_checked() {
    let dir = tempfile::tempdir().expect("tempdir");
    write_project(
        dir.path(),
        &[
            ("C1.lean", "import C2\ntheorem c1 : True := True.intro\n"),
            ("C2.lean", "import C1\ntheorem c2 : True := True.intro\n"),
            ("U.lean", "import C1\ntheorem u : (1 : Nat) = 1 := rfl\n"),
            ("V.lean", "import Bin\ntheorem v : (1 : Nat) = 1 := rfl\n"),
            ("W.lean", "import U\ntheorem w : (1 : Nat) = 1 := rfl\n"),
            ("Good.lean", "theorem g : (1 : Nat) = 1 := rfl\n"),
        ],
    );
    // Not UTF-8: unreadable, so never parsed.
    fs::write(dir.path().join("Bin.lean"), b"\xff\xfe bad\n").expect("write Bin");
    let (output, report) = check_project(dir.path());
    assert!(!output.status.success(), "{report}");
    assert_eq!(module_report(&report, "Bin")["parsed"], false, "{report}");
    for module in ["U", "V", "W"] {
        let entry = module_report(&report, module);
        assert_eq!(entry["status"], "import_failed", "{module}: {report}");
        assert_eq!(entry["checked"], false, "{module}: {report}");
        assert_eq!(usize_field(entry, "success_count"), 0, "{module}: {report}");
        assert!(
            entry["diagnostics"]
                .as_array()
                .expect("diagnostics")
                .iter()
                .any(|d| d["kind"] == "import_not_loaded"),
            "{module}: {report}"
        );
    }
    assert_eq!(module_report(&report, "Good")["status"], "pass", "{report}");
    assert_eq!(usize_field(&report["summary"], "declarations_passed"), 1);
}

const CLASS_C: &str = "class C where\n  v : Nat\n";

/// SIBLING-IMPORT LEAK THROUGH AN ATTRIBUTE (round-24 verification of
/// ff6c33c2c). `Q`'s `attribute [instance] c` bound `P`'s root `c` whenever
/// `P` was in the environment — although `Q` does not import `P` — while Lean
/// 4.8.0 (which compiles `Q` without `P`) registers `N.c`. `Q` adds the same
/// constants both ways, so the constants-only divergence check saw nothing,
/// and `theorem m : C.v = 3 := rfl` passed BOTH `clean check M` and `clean
/// project check` (exit 0) where Lean rejects `M`. In `b_attr_unknown`, `Q`
/// names `N.c`, which only the unimported `P` defines: Lean cannot compile
/// `Q`, and `project check` still counted `m` in `declarations_passed` under
/// `import_failed`. Every shape must now be refused by both commands, and
/// credit nothing that says `C.v = 3`.
#[test]
fn an_attribute_resolved_through_an_unimported_sibling_is_not_credited() {
    let q_open = "import B\nnamespace N\ndef c : C := ⟨2⟩\nend N\nopen N\nattribute [instance] c\n";
    let q_inside = "import B\nnamespace N\ndef c : C := ⟨2⟩\nattribute [instance] c\nend N\n";
    let q_unknown = "import B\ndef q : Nat := 0\nattribute [instance] N.c\n";
    let p_root = "import B\ndef c : C := ⟨3⟩\n";
    let p_n = "import B\ndef N.c : C := ⟨3⟩\n";
    for (label, p, q, via_x, q_first) in [
        ("open N", p_root, q_open, false, false),
        ("open N, Q imported first", p_root, q_open, false, true),
        ("inside namespace N", p_root, q_inside, false, false),
        ("open N through an aggregator", p_root, q_open, true, false),
        (
            "inside N through an aggregator",
            p_root,
            q_inside,
            true,
            false,
        ),
        ("target only in the sibling", p_n, q_unknown, true, false),
        (
            "target only in the sibling, direct",
            p_n,
            q_unknown,
            false,
            false,
        ),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let imports = if q_first {
            "import Q\nimport P\n"
        } else {
            "import P\nimport Q\n"
        };
        let m = if via_x {
            "import X\ntheorem m : C.v = 3 := rfl\n".to_string()
        } else {
            format!("{imports}theorem m : C.v = 3 := rfl\n")
        };
        let mut files = vec![
            ("B.lean", CLASS_C),
            ("P.lean", p),
            ("Q.lean", q),
            ("M.lean", m.as_str()),
        ];
        if via_x {
            files.push(("X.lean", imports));
        }
        write_project(dir.path(), &files);

        let (output, report) = check_project(dir.path());
        assert!(!output.status.success(), "{label}: {report}");
        let entry = module_report(&report, "M");
        assert_ne!(entry["status"], "pass", "{label}: {report}");
        // `m` is credited nowhere: either it was not checked, it failed, or
        // it checked against a failed import (not credited).
        let summary = &report["summary"];
        let credited_m = entry["failed_imports"]
            .as_array()
            .expect("failed_imports")
            .is_empty()
            && usize_field(entry, "success_count") > 0;
        assert!(!credited_m, "{label}: `m` credited: {report}");
        assert_eq!(
            usize_field(summary, "declarations_passed")
                + usize_field(summary, "declarations_failed")
                + usize_field(summary, "declarations_not_credited"),
            usize_field(summary, "declarations_checked"),
            "{label}: {report}"
        );

        let (check_output, check_report) = clean_check_json(&dir.path().join("M.lean"));
        assert!(
            !check_output.status.success(),
            "{label}: clean check M: {check_report}"
        );
    }
}

/// The controls: what Lean 4.8.0 ACCEPTS is not refused as a divergence.
/// Two siblings each registering an instance of the same class leave
/// different instance vectors next to each other than alone — only the
/// instance each registers is its effect — and a namespace-resolved
/// attribute agrees with its isolated elaboration.
#[test]
fn sibling_instance_registrations_that_lean_accepts_are_not_divergences() {
    for (label, p, q, claim) in [
        (
            "two instances of one class",
            "import B\ninstance p : C := ⟨3⟩\n",
            "import B\ninstance q : C := ⟨2⟩\n",
            "theorem m : C.v = 2 := rfl\n",
        ),
        (
            "attribute inside namespace N",
            "import B\ndef c : C := ⟨3⟩\n",
            "import B\nnamespace N\ndef c : C := ⟨2⟩\nattribute [instance] c\nend N\n",
            "theorem m : C.v = 2 := rfl\n",
        ),
    ] {
        let dir = tempfile::tempdir().expect("tempdir");
        let m = format!("import P\nimport Q\n{claim}");
        write_project(
            dir.path(),
            &[
                ("B.lean", CLASS_C),
                ("P.lean", p),
                ("Q.lean", q),
                ("M.lean", m.as_str()),
            ],
        );
        let (output, report) = check_project(dir.path());
        assert!(output.status.success(), "{label}: {report}");
        assert_eq!(
            module_report(&report, "M")["status"],
            "pass",
            "{label}: {report}"
        );
        assert!(
            blocker_messages(&report, "import_environment_divergence").is_empty(),
            "{label}: {report}"
        );
        let (check_output, check_report) = clean_check_json(&dir.path().join("M.lean"));
        assert!(
            check_output.status.success(),
            "{label}: clean check M: {check_report}"
        );
        assert_eq!(usize_field(&check_report, "success_count"), 1, "{label}");
    }
}

/// ROUND-25 VERIFICATION OF 3ee5ff78e. Four shapes in which `clean check`
/// and/or `clean project check` credited `C.v = x` for a value Lean 4.8.0
/// does not give `C.v` in `M` (every row measured on Lean 4.8.0,
/// `scratchpad/round25/project-check/verify0/{va,vb}`):
///
/// * import order (`project check` only): with `M: import Q; import P`, Lean
///   loads P's instance last and takes it; `project check` replayed the
///   closure in its own module order and took Q's.
/// * `local instance` / `scoped instance` in an imported module stayed in
///   force (both commands).
/// * `attribute [instance] c` inside `namespace N` bound an imported
///   `protected def N.c` (both commands).
///
/// For each shape, `M` stating Lean's value must pass both commands and `M`
/// stating the other value must pass neither.
#[test]
fn an_importer_sees_the_instance_lean_gives_it() {
    let b = CLASS_C;
    let b_i2 = "class C where\n  v : Nat\ninstance i2 : C := ⟨2⟩\n";
    let b_c2 = "class C where\n  v : Nat\ndef c : C := ⟨2⟩\n";
    let i3 = "import B\ninstance i3 : C := ⟨3⟩\n";
    let i2 = "import B\ninstance i2 : C := ⟨2⟩\n";
    let cases: &[(&str, Vec<(&str, &str)>, &str, u32, u32)] = &[
        (
            "ord_QP",
            vec![("B.lean", b), ("P.lean", i3), ("Q.lean", i2)],
            "import Q\nimport P\n",
            3,
            2,
        ),
        (
            "ord_PQ",
            vec![("B.lean", b), ("P.lean", i3), ("Q.lean", i2)],
            "import P\nimport Q\n",
            2,
            3,
        ),
        (
            "dia_QP",
            vec![
                ("B.lean", b),
                ("P.lean", i3),
                ("Q.lean", i2),
                ("R.lean", "import P\n"),
                ("S.lean", "import Q\n"),
            ],
            "import S\nimport R\n",
            3,
            2,
        ),
        (
            "local",
            vec![
                ("B.lean", b_i2),
                (
                    "P.lean",
                    "import B\nlocal instance i3 : C := ⟨3⟩\ntheorem p : C.v = 3 := rfl\n",
                ),
            ],
            "import P\n",
            2,
            3,
        ),
        (
            "scoped",
            vec![
                ("B.lean", b_i2),
                (
                    "P.lean",
                    "import B\nnamespace N\nscoped instance i3 : C := ⟨3⟩\nend N\nopen N\n",
                ),
            ],
            "import P\n",
            2,
            3,
        ),
        (
            "scoped, opened",
            vec![
                ("B.lean", b_i2),
                (
                    "P.lean",
                    "import B\nnamespace N\nscoped instance i3 : C := ⟨3⟩\nend N\n",
                ),
            ],
            "import P\nopen N\n",
            3,
            2,
        ),
        (
            "protected",
            vec![
                ("B.lean", b_c2),
                (
                    "P.lean",
                    "import B\nnamespace N\nprotected def c : C := ⟨3⟩\nend N\n",
                ),
            ],
            "import P\nnamespace N\nattribute [instance] c\nend N\n",
            2,
            3,
        ),
    ];
    for (label, files, header, lean_value, other_value) in cases {
        for (value, lean_accepts) in [(lean_value, true), (other_value, false)] {
            let dir = tempfile::tempdir().expect("tempdir");
            let m = format!("{header}theorem m : C.v = {value} := rfl\n");
            let mut all = files.clone();
            all.push(("M.lean", m.as_str()));
            write_project(dir.path(), &all);

            let (_, report) = check_project(dir.path());
            let entry = module_report(&report, "M");
            assert_eq!(
                entry["status"] == "pass",
                lean_accepts,
                "{label}, C.v = {value}: project check: {report}"
            );
            let (output, check) = clean_check_json(&dir.path().join("M.lean"));
            assert_eq!(
                output.status.success(),
                lean_accepts,
                "{label}, C.v = {value}: clean check: {check}"
            );
        }
    }
}
