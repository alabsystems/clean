// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! `/` and `%` on `Int` mean what Lean means (E-rounding `Int.ediv` /
//! `Int.emod`), and `Int.fdiv`/`Int.fmod`/`Int.natAbs`/`Int.sign` exist with
//! Lean's values, through the real `clean check` on the default prelude
//! (`docs/DECISIONS.md` R168).
//!
//! Measured 2026-10-26 (R164 item 3) with `clean 0.9.0+g415e0e9cb`: `clean
//! check` ACCEPTED `(-7 : Int) / 2 = -3 := by decide` and `(-1 : Int) % 256 =
//! -1 := by decide` and refuted the true `-4` and `255`, because
//! `instHDivInt`/`instHModInt` wrapped the T-rounding `Int.div`/`Int.mod`.
//! `d14090901` re-pointed them at checked `Int.ediv`/`Int.emod`.
//!
//! Every verdict below was read off Lean itself on 2026-10-27: each `ACCEPT`
//! theorem is proved, and each `REFUSE` theorem refuted, by `lean` v4.8.0 and
//! by v4.30.0-rc2 (on v4.30, which has no `Int.div`/`Int.mod`, the two
//! T-rounding rows were checked as `Int.tdiv`/`Int.tmod`). The refusal rows
//! are the negative control: a prelude that accepted anything would pass
//! the accept rows and fail here.

#![cfg(unix)]

use std::fs;
use std::path::PathBuf;
use std::process::Command;

fn clean_path() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_clean"))
}

/// `(name, statement, proof, Lean's verdict)`.
const ROWS: &[(&str, &str, &str, bool)] = &[
    // The two probes R164 recorded, refuted, and their true values accepted.
    ("probe_div_trunc", "(-7 : Int) / 2 = -3", "by decide", false),
    (
        "probe_mod_trunc",
        "(-1 : Int) % 256 = -1",
        "by decide",
        false,
    ),
    ("probe_div_true", "(-7 : Int) / 2 = -4", "by decide", true),
    (
        "probe_mod_true",
        "(-1 : Int) % 256 = 255",
        "by decide",
        true,
    ),
    ("probe_div_trunc_rfl", "(-7 : Int) / 2 = -3", "rfl", false),
    ("probe_mod_trunc_rfl", "(-1 : Int) % 256 = -1", "rfl", false),
    ("probe_div_true_rfl", "(-7 : Int) / 2 = -4", "rfl", true),
    ("probe_mod_true_rfl", "(-1 : Int) % 256 = 255", "rfl", true),
    // Every sign pair, and zero divisors.
    ("ediv_pos_neg", "(7 : Int) / (-2) = -3", "by decide", true),
    ("ediv_neg_neg", "(-7 : Int) / (-2) = 4", "by decide", true),
    (
        "ediv_neg_neg_trunc",
        "(-7 : Int) / (-2) = 3",
        "by decide",
        false,
    ),
    ("emod_neg_neg", "(-7 : Int) % (-2) = 1", "by decide", true),
    ("emod_pos_neg", "(7 : Int) % (-2) = 1", "by decide", true),
    ("ediv_by_zero", "(-5 : Int) / 0 = 0", "by decide", true),
    ("emod_by_zero", "(-5 : Int) % 0 = -5", "by decide", true),
    (
        "emod_by_zero_wrong",
        "(-5 : Int) % 0 = 0",
        "by decide",
        false,
    ),
    // Named heads: E, T (Lean 4.8.0's `Int.div`/`Int.mod`) and F rounding.
    ("named_ediv", "Int.ediv (-7) 2 = -4", "by decide", true),
    ("named_emod", "Int.emod (-7) 2 = 1", "by decide", true),
    ("named_tdiv", "Int.div (-7) 2 = -3", "by decide", true),
    ("named_tmod", "Int.mod (-7) 2 = -1", "by decide", true),
    (
        "named_tdiv_wrong",
        "Int.div (-7) 2 = -4",
        "by decide",
        false,
    ),
    ("named_fdiv", "Int.fdiv 7 (-2) = -4", "by decide", true),
    ("named_fmod", "Int.fmod 7 (-2) = -1", "by decide", true),
    ("named_fmod_neg", "Int.fmod (-7) 2 = 1", "by decide", true),
    (
        "named_fdiv_wrong",
        "Int.fdiv 7 (-2) = -3",
        "by decide",
        false,
    ),
    // A zero dividend over a negative divisor: Lean's `fdiv`/`fmod` take
    // their `0, _ => 0` case here, and `ofNat (succ m), -[n+1]` splits the
    // dividend, so a body that skips the zero/successor split (`-[0 / 2 +1]`
    // = -1) or returns the divisor's magnitude (1) is caught only by a zero
    // dividend.
    ("fdiv_zero_negdiv", "Int.fdiv 0 (-2) = 0", "by decide", true),
    (
        "fdiv_zero_negdiv_wrong",
        "Int.fdiv 0 (-2) = -1",
        "by decide",
        false,
    ),
    ("fmod_zero_negdiv", "Int.fmod 0 (-2) = 0", "by decide", true),
    (
        "fmod_zero_negdiv_wrong",
        "Int.fmod 0 (-2) = 1",
        "by decide",
        false,
    ),
    ("named_fdiv_zero", "Int.fdiv (-7) 0 = 0", "rfl", true),
    ("named_fmod_zero", "Int.fmod (-7) 0 = -7", "rfl", true),
    // A remainder whose magnitude is 2^63: Lean's `subNatNat` is one case on
    // `n - m`, so this is a single step, not 2^63 decrements.
    (
        "emod_big",
        "(-9223372036854775808 : Int) % 18446744073709551616 = 9223372036854775808",
        "by decide",
        true,
    ),
    // The same statements through `norm_num`, `simp` and `omega`, whose closes
    // the kernel re-checks. `simp` and `omega` verdicts are Lean 4.8.0's and
    // v4.30.0-rc2's; Lean core has no `norm_num`, so its rows carry the
    // statement's truth (Lean's `decide`).
    (
        "tac_norm_num_div",
        "(-7 : Int) / 2 = -4",
        "by norm_num",
        true,
    ),
    (
        "tac_norm_num_div_wrong",
        "(-7 : Int) / 2 = -3",
        "by norm_num",
        false,
    ),
    (
        "tac_norm_num_mod",
        "(-1 : Int) % 256 = 255",
        "by norm_num",
        true,
    ),
    (
        "tac_norm_num_mod_wrong",
        "(-1 : Int) % 256 = -1",
        "by norm_num",
        false,
    ),
    (
        "tac_norm_num_mod2",
        "(-7 : Int) % 2 = 1",
        "by norm_num",
        true,
    ),
    ("tac_simp_div", "(-7 : Int) / 2 = -4", "by simp", true),
    (
        "tac_simp_div_wrong",
        "(-7 : Int) / 2 = -3",
        "by simp",
        false,
    ),
    ("tac_simp_mod", "(-1 : Int) % 256 = 255", "by simp", true),
    (
        "tac_simp_mod_wrong",
        "(-1 : Int) % 256 = -1",
        "by simp",
        false,
    ),
    ("tac_omega_div", "(-7 : Int) / 2 = -4", "by omega", true),
    (
        "tac_omega_div_wrong",
        "(-7 : Int) / 2 = -3",
        "by omega",
        false,
    ),
    ("tac_omega_mod", "(-1 : Int) % 256 = 255", "by omega", true),
    (
        "tac_omega_mod_wrong",
        "(-1 : Int) % 256 = -1",
        "by omega",
        false,
    ),
    ("natabs_neg", "Int.natAbs (-7) = 7", "by decide", true),
    ("sign_neg", "Int.sign (-7) = -1", "by decide", true),
    ("sign_zero_wrong", "Int.sign 0 = 1", "by decide", false),
];

#[test]
fn int_division_and_remainder_match_lean() {
    let dir = tempfile::tempdir().expect("tempdir");
    let mut src = String::new();
    for (name, stmt, proof, _) in ROWS {
        src.push_str(&format!("theorem {name} : {stmt} := {proof}\n"));
    }
    fs::write(dir.path().join("int_div.lean"), &src).expect("write probe file");
    let output = Command::new(clean_path())
        .args(["check", "--json", "int_div.lean"])
        .current_dir(dir.path())
        .output()
        .expect("run clean check");
    let report = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        report.contains("\"schema_version\": \"Clean-check-report-v2\""),
        "no v2 report\nstdout:\n{report}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    // A row counts as refused when an error names it. That alone would read
    // an ACCEPT row whose failure is reported without the `<name>: ` prefix
    // as accepted, so the report's own counts must also equal the rows'
    // verdicts: every refusal the report counts is one the name check saw.
    let accepts = ROWS.iter().filter(|row| row.3).count();
    let refusals = ROWS.len() - accepts;
    assert_eq!(count(&report, "decl_count"), ROWS.len(), "{report}");
    assert_eq!(count(&report, "diverged_count"), 0, "{report}");
    let mut wrong = Vec::new();
    let mut named_failures = 0;
    for (name, stmt, proof, lean_accepts) in ROWS {
        let seen = report.contains(&format!("\"name\": \"{name}\""));
        let failed = report.contains(&format!("\"{name}: "));
        assert!(seen, "{name} was not checked at all:\n{report}");
        named_failures += usize::from(failed);
        let clean_accepts = !failed;
        if clean_accepts != *lean_accepts {
            wrong.push(format!(
                "{name}: `{stmt} := {proof}`: Lean {}, clean {}",
                if *lean_accepts { "accepts" } else { "refutes" },
                if clean_accepts { "accepts" } else { "refuses" },
            ));
        }
    }
    assert!(
        wrong.is_empty(),
        "verdicts that differ from Lean's:\n{}\n\nreport:\n{report}",
        wrong.join("\n")
    );
    assert_eq!(
        (
            count(&report, "failed_count"),
            count(&report, "success_count")
        ),
        (named_failures, ROWS.len() - named_failures),
        "the report counts a failure no error names\n{report}"
    );
    assert_eq!(named_failures, refusals, "{report}");
}

/// The integer a top-level `"key": N` field of the report holds.
fn count(report: &str, key: &str) -> usize {
    let tag = format!("\n  \"{key}\": ");
    let at = report
        .find(&tag)
        .unwrap_or_else(|| panic!("no top-level {key} in\n{report}"));
    let digits: String = report[at + tag.len()..]
        .chars()
        .take_while(char::is_ascii_digit)
        .collect();
    digits
        .parse()
        .unwrap_or_else(|_| panic!("{key} is not a count in\n{report}"))
}
