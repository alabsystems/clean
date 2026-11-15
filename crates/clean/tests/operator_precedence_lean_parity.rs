// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `^` (`infixr:80`) binds tighter than the shifts `<<<`/`>>>` (`infixl:75`)
//! on either side, as in Lean 4.8.0 (`Init/Notation.lean:280-282`), through
//! the real `clean check` on the default prelude.
//!
//! Measured 2026-10-29 with `clean` at `a9203a200` (the inc8 differential
//! hunt, 4,686 operator-pair files judged by Lean 4.8.0): `clean check`
//! ACCEPTED 23 statements Lean refutes, every one a `^` beside a shift, e.g.
//! `(6 &&& 9 ^ 2 <<< 2 : Nat) ≠ 4 := by decide` (Lean: it is 4) and
//! `(5 >>> 2 ^ 3 : Nat) = 1 := rfl` (Lean: 0), because the parser put `^` at
//! the shifts' level 75 and parsed `9 ^ 2 <<< 2` as `9 ^ (2 <<< 2)`.
//!
//! Every verdict below was read off `lean` v4.8.0 on 2026-10-29: each `true`
//! theorem is proved and each `false` one refused there. The refusal rows are
//! the negative control: the old parse accepts every one of them and refuses
//! the true rows beside them.

#![cfg(unix)]

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// `(name, statement, proof, Lean's verdict)`.
const ROWS: &[(&str, &str, &str, bool)] = &[
    (
        "shl_after_pow",
        "(6 ^ 3 <<< 2 : Nat) = 864",
        "by decide",
        true,
    ),
    (
        "shl_after_pow_wrong",
        "(6 ^ 3 <<< 2 : Nat) ≠ 864",
        "by decide",
        false,
    ),
    (
        "shl_after_pow_old",
        "(6 ^ 3 <<< 2 : Nat) = 6 ^ 12",
        "by decide",
        false,
    ),
    (
        "shr_after_pow",
        "(2 ^ 5 >>> 3 : Nat) = 4",
        "by decide",
        true,
    ),
    (
        "shr_after_pow_wrong",
        "(2 ^ 5 >>> 3 : Nat) ≠ 4",
        "by decide",
        false,
    ),
    (
        "pow_under_shl",
        "(6 <<< 3 ^ 2 : Nat) = 3072",
        "by decide",
        true,
    ),
    (
        "pow_under_shl_wrong",
        "(6 <<< 3 ^ 2 : Nat) ≠ 3072",
        "by decide",
        false,
    ),
    (
        "pow_under_shr",
        "(5 >>> 2 ^ 3 : Nat) = 0",
        "by decide",
        true,
    ),
    (
        "pow_under_shr_old",
        "(5 >>> 2 ^ 3 : Nat) = 1",
        "by decide",
        false,
    ),
    (
        "pow_under_shr_old_rfl",
        "(5 >>> 2 ^ 3 : Nat) = 1",
        "rfl",
        false,
    ),
    ("pow_one_shr", "(1 ^ 7 >>> 2 : Nat) = 0", "rfl", true),
    ("pow_one_shr_old", "(1 ^ 7 >>> 2 : Nat) = 1", "rfl", false),
    (
        "and_pow_shl",
        "(6 &&& 9 ^ 2 <<< 2 : Nat) = 4",
        "by decide",
        true,
    ),
    (
        "and_pow_shl_wrong",
        "(6 &&& 9 ^ 2 <<< 2 : Nat) ≠ 4",
        "by decide",
        false,
    ),
    (
        "shl_chain",
        "(7 <<< 3 <<< 1 ^ 2 / 8 &&& 8 : Nat) = 8",
        "by decide",
        true,
    ),
    (
        "shl_chain_wrong",
        "(7 <<< 3 <<< 1 ^ 2 / 8 &&& 8 : Nat) ≠ 8",
        "by decide",
        false,
    ),
    (
        "shl_left_assoc",
        "(3 <<< 1 <<< 2 : Nat) = 24",
        "by decide",
        true,
    ),
    (
        "shl_left_assoc_wrong",
        "(3 <<< 1 <<< 2 : Nat) = 48",
        "by decide",
        false,
    ),
    (
        "pow_right_assoc",
        "(2 ^ 3 ^ 2 : Nat) = 512",
        "by decide",
        true,
    ),
    (
        "pow_right_assoc_wrong",
        "(2 ^ 3 ^ 2 : Nat) = 64",
        "by decide",
        false,
    ),
    ("mul_shl", "(2 * 3 <<< 1 : Nat) = 12", "by decide", true),
    ("shl_mul", "(2 <<< 3 * 2 : Nat) = 32", "by decide", true),
    (
        "shl_mul_wrong",
        "(2 <<< 3 * 2 : Nat) = 128",
        "by decide",
        false,
    ),
    ("neg_pow", "(-2 ^ 2 : Int) = -4", "by decide", true),
    ("neg_pow_wrong", "(-2 ^ 2 : Int) = 4", "by decide", false),
    // A user operator between the shifts (75) and `^` (80), declared in
    // [`PRELUDE`]: `^`'s right operand is at level 80 (`⊞`, level 78, is not
    // in it), and an operand at level 77 or 79 takes `^` (a parse of those
    // levels below `^` read `1 ⊞ 2 ^ 3` as `(1 ⊞ 2) ^ 3`).
    (
        "custom78_after_pow",
        "(2 ^ 3 ⊞ 1 : Nat) = 9",
        "by decide",
        true,
    ),
    (
        "custom78_after_pow_wrong",
        "(2 ^ 3 ⊞ 1 : Nat) = 16",
        "by decide",
        false,
    ),
    ("custom78_pow", "(1 ⊞ 2 ^ 3 : Nat) = 9", "by decide", true),
    (
        "custom78_pow_wrong",
        "(1 ⊞ 2 ^ 3 : Nat) = 27",
        "by decide",
        false,
    ),
    ("custom76_pow", "(1 ⊟ 2 ^ 3 : Nat) = 9", "by decide", true),
    (
        "custom76_pow_wrong",
        "(1 ⊟ 2 ^ 3 : Nat) = 27",
        "by decide",
        false,
    ),
    ("custom79_pow", "(2 ⊠ 3 ^ 2 : Nat) = 18", "by decide", true),
    (
        "custom79_pow_wrong",
        "(2 ⊠ 3 ^ 2 : Nat) = 36",
        "by decide",
        false,
    ),
    (
        "custom79_shl",
        "(1 <<< 2 ⊠ 3 : Nat) = 64",
        "by decide",
        true,
    ),
    (
        "custom79_shl_wrong",
        "(1 <<< 2 ⊠ 3 : Nat) = 12",
        "by decide",
        false,
    ),
];

/// The user operators the `custom*` rows use, at levels 76, 78 and 79.
const PRELUDE: &str = "infixl:78 \" ⊞ \" => Nat.add\n\
                       infixl:76 \" ⊟ \" => Nat.add\n\
                       infixr:79 \" ⊠ \" => Nat.mul\n";

#[test]
fn pow_and_shift_precedence_match_lean() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut src = String::from(PRELUDE);
    for (name, stmt, proof, _) in ROWS {
        src.push_str(&format!("theorem {name} : {stmt} := {proof}\n"));
    }
    fs::write(dir.path().join("prec.lean"), &src).expect("write probe file");
    let output = Command::new(clean_path())
        .args(["check", "--json", "prec.lean"])
        .current_dir(dir.path())
        .output()
        .expect("run clean check");
    let report = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        report.contains("\"schema_version\": \"Clean-check-report-v2\""),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    // A row counts as refused when an error names it; the report's own counts
    // must agree, so a failure reported without the `<name>: ` prefix cannot
    // read as an accept.
    let accepts = ROWS.iter().filter(|row| row.3).count();
    assert_eq!(count(&report, "decl_count"), ROWS.len(), "{report}");
    let mut wrong = Vec::new();
    let mut named_failures = 0;
    for (name, stmt, proof, lean_accepts) in ROWS {
        assert!(
            report.contains(&format!("\"name\": \"{name}\"")),
            "{name} was not checked at all:\n{report}"
        );
        let failed = report.contains(&format!("\"{name}: "));
        named_failures += usize::from(failed);
        if failed == *lean_accepts {
            wrong.push(format!(
                "{name}: `{stmt} := {proof}`: Lean {}, clean {}",
                if *lean_accepts { "accepts" } else { "refutes" },
                if failed { "refuses" } else { "accepts" },
            ));
        }
    }
    assert!(wrong.is_empty(), "{}", wrong.join("\n"));
    assert_eq!(
        (
            count(&report, "failed_count"),
            count(&report, "success_count")
        ),
        (named_failures, ROWS.len() - named_failures),
    );
    assert_eq!(ROWS.len() - named_failures, accepts, "{report}");
}

/// The integer a top-level `"key": N` field of the report holds.
fn count(report: &str, key: &str) -> usize {
    let tag = format!("\n  \"{key}\": ");
    let at = report
        .find(&tag)
        .unwrap_or_else(|| panic!("no top-level {key} in\n{report}"));
    report[at + tag.len()..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect::<String>()
        .parse()
        .unwrap_or_else(|_| panic!("{key} is not a count in\n{report}"))
}
