#![forbid(unsafe_code)]
// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit C2 executable qualification (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`):
//! builds and runs `kcheck-labelled-cases` from a clean scratch copy of the four
//! theory packages (`cic_l`, `cic_l_model`, `kcheck_spec`, `kcheck_labelled`),
//! asserting byte-for-byte stdout equality with `expected_output.txt`, structural
//! case/summary reconciliation (`115` cases: `43` accepted, `72` refused), and
//! 8 synthetic negative controls.
//!
//! Standing limits:
//! 1. Validates pinned-Lean C-backend execution of the C2 case runner by design;
//!    this is not Trust-compiled execution (W1/X2/X3).
//! 2. Soundness is per explicit finite universe bound `N` and relative to the
//!    stated base theory (`Ax0`).
//! 3. By design `KCheck.checker` is to become the proved checker once all six
//!    Plan §2.1 conditions hold in fact; the independent re-checker quorum stays.

use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const REQUIRED_PACKAGES: [&str; 4] = ["cic_l", "cic_l_model", "kcheck_spec", "kcheck_labelled"];
const EXE_NAME: &str = "kcheck-labelled-cases";
const EXE_ROOT: &str = "KCheckLabelledMain";

struct RunResult {
    returncode: i32,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    exe_exists: bool,
}

fn check_toolchain_pins(repo_root: &Path) -> Result<String, String> {
    let root_pin_path = repo_root.join("lean-toolchain");
    let root_pin = fs::read_to_string(&root_pin_path)
        .map_err(|e| {
            format!(
                "missing workspace lean-toolchain {}: {e}",
                root_pin_path.display()
            )
        })?
        .trim()
        .to_string();
    if root_pin.is_empty() {
        return Err("workspace lean-toolchain is empty".to_string());
    }
    for pkg in REQUIRED_PACKAGES {
        let pkg_pin_path = repo_root.join(format!("theories/{pkg}/lean-toolchain"));
        let pkg_pin = fs::read_to_string(&pkg_pin_path)
            .map_err(|e| {
                format!(
                    "missing package lean-toolchain {}: {e}",
                    pkg_pin_path.display()
                )
            })?
            .trim()
            .to_string();
        if pkg_pin != root_pin {
            return Err(format!(
                "toolchain mismatch for theories/{pkg}: `{pkg_pin}` != workspace `{root_pin}`"
            ));
        }
    }
    Ok(root_pin)
}

fn check_lakefile_contract(lakefile_path: &Path) -> Result<(), String> {
    let raw = fs::read_to_string(lakefile_path)
        .map_err(|e| format!("missing lakefile {}: {e}", lakefile_path.display()))?;
    let parsed: toml::Value = toml::from_str(&raw)
        .map_err(|e| format!("invalid TOML {}: {e}", lakefile_path.display()))?;
    let default_targets = parsed
        .get("defaultTargets")
        .and_then(toml::Value::as_array)
        .ok_or_else(|| "defaultTargets must be a list".to_string())?;
    if !default_targets.iter().any(|v| v.as_str() == Some(EXE_NAME)) {
        return Err(format!(
            "`defaultTargets` must contain `{EXE_NAME}`, got {default_targets:?}"
        ));
    }
    let exes = parsed
        .get("lean_exe")
        .and_then(toml::Value::as_array)
        .ok_or_else(|| "missing `[[lean_exe]]` table".to_string())?;
    let matched: Vec<&toml::Value> = exes
        .iter()
        .filter(|row| row.get("name").and_then(toml::Value::as_str) == Some(EXE_NAME))
        .collect();
    if matched.len() != 1 {
        return Err(format!(
            "expected exactly one `[[lean_exe]]` named `{EXE_NAME}`, got {}",
            matched.len()
        ));
    }
    if matched[0].get("root").and_then(toml::Value::as_str) != Some(EXE_ROOT) {
        return Err(format!(
            "`{EXE_NAME}` root must be `{EXE_ROOT}`, got {:?}",
            matched[0].get("root")
        ));
    }
    Ok(())
}

fn parse_summary_line(line: &str) -> Result<(usize, usize, usize), String> {
    let rest = line
        .strip_prefix("cases ")
        .ok_or_else(|| format!("malformed summary trailer: {line:?}"))?;
    let (total_s, rest) = rest
        .split_once(", accepted ")
        .ok_or_else(|| format!("malformed summary trailer: {line:?}"))?;
    let (acc_s, ref_s) = rest
        .split_once(", refused ")
        .ok_or_else(|| format!("malformed summary trailer: {line:?}"))?;
    let total: usize = total_s
        .parse()
        .map_err(|_| format!("invalid total count in {line:?}"))?;
    let acc: usize = acc_s
        .parse()
        .map_err(|_| format!("invalid accepted count in {line:?}"))?;
    let refused: usize = ref_s
        .parse()
        .map_err(|_| format!("invalid refused count in {line:?}"))?;
    Ok((total, acc, refused))
}

fn validate_output_structure(
    stdout: &[u8],
    expected: &[u8],
) -> Result<(usize, usize, usize), String> {
    if expected.is_empty() {
        return Err("expected_output.txt is empty".to_string());
    }
    if stdout != expected {
        return Err("kcheck-labelled-cases stdout differs from expected_output.txt".to_string());
    }
    let text = std::str::from_utf8(stdout).map_err(|e| format!("stdout not valid UTF-8: {e}"))?;
    if !text.ends_with('\n') {
        return Err("stdout must end with a trailing newline".to_string());
    }
    let lines: Vec<&str> = text.lines().collect();
    if lines.len() < 2 {
        return Err("stdout must contain case lines and summary".to_string());
    }
    let (declared_total, declared_acc, declared_ref) = parse_summary_line(lines[lines.len() - 1])?;
    if declared_total == 0 || declared_acc + declared_ref != declared_total {
        return Err("summary counts do not add up".to_string());
    }
    let case_lines = &lines[..lines.len() - 1];
    if case_lines.len() != declared_total {
        return Err(format!(
            "case line count ({}) != summary total ({declared_total})",
            case_lines.len()
        ));
    }
    let mut seen_names = BTreeSet::new();
    let mut actual_acc = 0_usize;
    let mut actual_ref = 0_usize;
    for (idx, line) in case_lines.iter().enumerate() {
        let (name, rhs) = line
            .split_once(": ")
            .ok_or_else(|| format!("malformed case verdict at line {}: {line:?}", idx + 1))?;
        if name.is_empty() || !name.bytes().all(|b| b.is_ascii_alphanumeric() || b == b'_') {
            return Err(format!("invalid case name at line {}: {name:?}", idx + 1));
        }
        if !seen_names.insert(name.to_string()) {
            return Err(format!("duplicate case name `{name}` at line {}", idx + 1));
        }
        if let Some(detail) = rhs.strip_prefix("accepted ") {
            if detail.is_empty() {
                return Err(format!("empty accepted detail at line {}", idx + 1));
            }
            actual_acc += 1;
        } else if let Some(detail) = rhs.strip_prefix("refused ") {
            if detail.is_empty() {
                return Err(format!("empty refused detail at line {}", idx + 1));
            }
            actual_ref += 1;
        } else {
            return Err(format!(
                "malformed case verdict at line {}: {line:?}",
                idx + 1
            ));
        }
    }
    if actual_acc != declared_acc || actual_ref != declared_ref {
        return Err(format!(
            "tallied verdicts (accepted={actual_acc}, refused={actual_ref}) != summary (accepted={declared_acc}, refused={declared_ref})"
        ));
    }
    Ok((declared_total, declared_acc, declared_ref))
}

fn copy_pkg_without_lake(src: &Path, dst: &Path) {
    fs::create_dir_all(dst).expect("mkdir dst");
    for entry in fs::read_dir(src).expect("read_dir src") {
        let entry = entry.expect("dir entry");
        let name = entry.file_name();
        if name.to_string_lossy() == ".lake" {
            continue;
        }
        let s = entry.path();
        let d = dst.join(name);
        if s.is_dir() {
            copy_pkg_without_lake(&s, &d);
        } else {
            fs::copy(&s, &d).expect("copy file");
        }
    }
}

fn build_and_run_in_scratch(repo_root: &Path, toolchain_bin: &Path) -> RunResult {
    let tmp = tempfile::tempdir().expect("scratch tempdir");
    let tmp_theories = tmp.path().join("theories");
    fs::create_dir_all(&tmp_theories).expect("mkdir theories");
    for pkg in REQUIRED_PACKAGES {
        copy_pkg_without_lake(
            &repo_root.join(format!("theories/{pkg}")),
            &tmp_theories.join(pkg),
        );
    }
    let pkg_dir = tmp_theories.join("kcheck_labelled");
    let exe_path = pkg_dir.join(".lake/build/bin").join(EXE_NAME);
    assert!(
        !exe_path.exists(),
        "fresh scratch copy unexpectedly contained {}",
        exe_path.display()
    );

    let mut path_entries: Vec<PathBuf> = vec![toolchain_bin.to_path_buf()];
    path_entries.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let joined_path = std::env::join_paths(path_entries).expect("join PATH");

    let build_out = Command::new(toolchain_bin.join("lake"))
        .args(["--no-cache", "build", EXE_NAME])
        .current_dir(&pkg_dir)
        .env("PATH", &joined_path)
        .env("LEAN_NUM_THREADS", "6")
        .output()
        .expect("run lake --no-cache build kcheck-labelled-cases");
    assert!(
        build_out.status.success(),
        "`lake --no-cache build {EXE_NAME}` failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&build_out.stdout),
        String::from_utf8_lossy(&build_out.stderr)
    );
    if !exe_path.is_file() {
        return RunResult {
            returncode: 0,
            stdout: Vec::new(),
            stderr: Vec::new(),
            exe_exists: false,
        };
    }
    let run_out = Command::new(&exe_path)
        .current_dir(&pkg_dir)
        .env("PATH", &joined_path)
        .output()
        .expect("execute kcheck-labelled-cases");
    RunResult {
        returncode: run_out.status.code().unwrap_or(-1),
        stdout: run_out.stdout,
        stderr: run_out.stderr,
        exe_exists: true,
    }
}

fn verify_repo_with_runner<F>(repo_root: &Path, runner: F) -> Result<(usize, usize, usize), String>
where
    F: FnOnce(&Path) -> RunResult,
{
    let _pin = check_toolchain_pins(repo_root)?;
    check_lakefile_contract(&repo_root.join("theories/kcheck_labelled/lakefile.toml"))?;
    let expected_path = repo_root.join("theories/kcheck_labelled/expected_output.txt");
    let expected_bytes = fs::read(&expected_path)
        .map_err(|e| format!("missing expected output {}: {e}", expected_path.display()))?;
    let res = runner(repo_root);
    if !res.exe_exists {
        return Err(format!(
            "build succeeded without producing `.lake/build/bin/{EXE_NAME}`"
        ));
    }
    if res.returncode != 0 {
        return Err(format!(
            "`{EXE_NAME}` exited non-zero: rc={}",
            res.returncode
        ));
    }
    if !res.stderr.is_empty() {
        return Err(format!(
            "`{EXE_NAME}` wrote unexpected stderr: {:?}",
            String::from_utf8_lossy(&res.stderr)
        ));
    }
    validate_output_structure(&res.stdout, &expected_bytes)
}

fn make_meta_tree(dst_root: &Path, repo_root: &Path) {
    fs::create_dir_all(dst_root).expect("mkdir meta root");
    fs::copy(
        repo_root.join("lean-toolchain"),
        dst_root.join("lean-toolchain"),
    )
    .expect("copy lean-toolchain");
    for pkg in REQUIRED_PACKAGES {
        let pkg_dir = dst_root.join(format!("theories/{pkg}"));
        fs::create_dir_all(&pkg_dir).expect("mkdir pkg");
        fs::copy(
            repo_root.join(format!("theories/{pkg}/lean-toolchain")),
            pkg_dir.join("lean-toolchain"),
        )
        .expect("copy pkg lean-toolchain");
    }
    fs::copy(
        repo_root.join("theories/kcheck_labelled/lakefile.toml"),
        dst_root.join("theories/kcheck_labelled/lakefile.toml"),
    )
    .expect("copy lakefile.toml");
    fs::copy(
        repo_root.join("theories/kcheck_labelled/expected_output.txt"),
        dst_root.join("theories/kcheck_labelled/expected_output.txt"),
    )
    .expect("copy expected_output.txt");
}

#[test]
fn kcheck_labelled_cases_executes_fresh_and_passes_eight_negative_controls() {
    let repo_root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let toolchain_bin = lean.parent().expect("toolchain bin dir");

    let (total, acc, refused) =
        verify_repo_with_runner(&repo_root, |r| build_and_run_in_scratch(r, toolchain_bin))
            .expect("live kcheck-labelled-cases build & execution must pass");
    assert_eq!(
        (total, acc, refused),
        (115, 43, 72),
        "expected exact 115 cases (43 accepted, 72 refused)"
    );

    let real_expected =
        fs::read(repo_root.join("theories/kcheck_labelled/expected_output.txt")).expect("read");
    let tmp = tempfile::tempdir().expect("selftest tempdir");

    // Arm 1: toolchain drift refused.
    let r1 = tmp.path().join("arm1");
    make_meta_tree(&r1, &repo_root);
    fs::write(
        r1.join("theories/kcheck_labelled/lean-toolchain"),
        "leanprover/lean4:v4.29.0\n",
    )
    .expect("write");
    assert!(verify_repo_with_runner(&r1, |_| RunResult {
        returncode: 0,
        stdout: real_expected.clone(),
        stderr: Vec::new(),
        exe_exists: true,
    })
    .unwrap_err()
    .contains("toolchain mismatch"));

    // Arm 2: executable dropped from defaultTargets refused.
    let r2 = tmp.path().join("arm2");
    make_meta_tree(&r2, &repo_root);
    let lf2 = r2.join("theories/kcheck_labelled/lakefile.toml");
    fs::write(
        &lf2,
        fs::read_to_string(&lf2).expect("read").replace(
            "defaultTargets = [\"KCheckLabelled\", \"kcheck-labelled-cases\"]",
            "defaultTargets = [\"KCheckLabelled\"]",
        ),
    )
    .expect("write");
    assert!(verify_repo_with_runner(&r2, |_| RunResult {
        returncode: 0,
        stdout: real_expected.clone(),
        stderr: Vec::new(),
        exe_exists: true,
    })
    .unwrap_err()
    .contains("defaultTargets"));

    // Arm 3: wrong [[lean_exe]] root refused.
    let r3 = tmp.path().join("arm3");
    make_meta_tree(&r3, &repo_root);
    let lf3 = r3.join("theories/kcheck_labelled/lakefile.toml");
    fs::write(
        &lf3,
        fs::read_to_string(&lf3)
            .expect("read")
            .replace("root = \"KCheckLabelledMain\"", "root = \"WrongMain\""),
    )
    .expect("write");
    assert!(verify_repo_with_runner(&r3, |_| RunResult {
        returncode: 0,
        stdout: real_expected.clone(),
        stderr: Vec::new(),
        exe_exists: true,
    })
    .unwrap_err()
    .contains("root must be"));

    // Arm 4: stdout drift refused.
    let r4 = tmp.path().join("arm4");
    make_meta_tree(&r4, &repo_root);
    let exp4 = r4.join("theories/kcheck_labelled/expected_output.txt");
    fs::write(
        &exp4,
        fs::read_to_string(&exp4).expect("read").replacen(
            "refl: accepted idNat bound 2 []",
            "refl: refused Refusal.refl",
            1,
        ),
    )
    .expect("write");
    assert!(verify_repo_with_runner(&r4, |_| RunResult {
        returncode: 0,
        stdout: real_expected.clone(),
        stderr: Vec::new(),
        exe_exists: true,
    })
    .unwrap_err()
    .contains("stdout differs"));

    // Arm 5: forged summary counts refused.
    let forged_summary = String::from_utf8(real_expected.clone())
        .expect("utf8")
        .replace(
            "cases 115, accepted 43, refused 72",
            "cases 115, accepted 44, refused 71",
        )
        .into_bytes();
    let r5 = tmp.path().join("arm5");
    make_meta_tree(&r5, &repo_root);
    fs::write(
        r5.join("theories/kcheck_labelled/expected_output.txt"),
        &forged_summary,
    )
    .expect("write");
    assert!(verify_repo_with_runner(&r5, |_| RunResult {
        returncode: 0,
        stdout: forged_summary,
        stderr: Vec::new(),
        exe_exists: true,
    })
    .unwrap_err()
    .contains("tallied verdicts"));

    // Arm 6: duplicate case name refused.
    let dup_lines = String::from_utf8(real_expected.clone())
        .expect("utf8")
        .replacen(
            "pi: accepted idNat bound 2 []",
            "refl: accepted idNat bound 2 []",
            1,
        )
        .into_bytes();
    let r6 = tmp.path().join("arm6");
    make_meta_tree(&r6, &repo_root);
    fs::write(
        r6.join("theories/kcheck_labelled/expected_output.txt"),
        &dup_lines,
    )
    .expect("write");
    assert!(verify_repo_with_runner(&r6, |_| RunResult {
        returncode: 0,
        stdout: dup_lines,
        stderr: Vec::new(),
        exe_exists: true,
    })
    .unwrap_err()
    .contains("duplicate case name"));

    // Arm 7: non-empty stderr refused.
    let r7 = tmp.path().join("arm7");
    make_meta_tree(&r7, &repo_root);
    assert!(verify_repo_with_runner(&r7, |_| RunResult {
        returncode: 0,
        stdout: real_expected.clone(),
        stderr: b"warning: unexpected\n".to_vec(),
        exe_exists: true,
    })
    .unwrap_err()
    .contains("unexpected stderr"));

    // Arm 8: missing built executable refused.
    let r8 = tmp.path().join("arm8");
    make_meta_tree(&r8, &repo_root);
    assert!(verify_repo_with_runner(&r8, |_| RunResult {
        returncode: 0,
        stdout: Vec::new(),
        stderr: Vec::new(),
        exe_exists: false,
    })
    .unwrap_err()
    .contains("without producing"));
}
