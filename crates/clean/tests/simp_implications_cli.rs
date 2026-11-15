// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The G12 fix through the public `clean check` caller and its JSON verdict.

use std::process::Command;

#[test]
fn cases_simp_implication_repro_and_false_twin() {
    let dir = tempfile::tempdir().expect("temporary project");
    for (name, source, accepted) in [
        (
            "G12.lean",
            include_str!(
                "../../../reports/trust-ir-semantics-probe/repros/G12-cases-simp-bool-match.lean"
            ),
            true,
        ),
        (
            "G12Twin.lean",
            include_str!(
                "../../../reports/trust-ir-semantics-probe/repros/G12-cases-simp-bool-match-twin.lean"
            ),
            false,
        ),
    ] {
        let file = dir.path().join(name);
        std::fs::write(&file, source).expect("write source");
        let output = Command::new(env!("CARGO_BIN_EXE_clean"))
            .args(["check", "--json"])
            .arg(&file)
            .output()
            .expect("run clean check");
        let report: serde_json::Value = serde_json::from_slice(&output.stdout)
            .unwrap_or_else(|e| panic!("{name}: {e}; stdout={:?}", output.stdout));
        assert_eq!(output.status.success(), accepted, "{name}: {report}");
        assert_eq!(report["decl_count"], 4, "{report}");
        assert_eq!(report["trust_summary"]["sorry_axioms"], 0, "{report}");
        assert_eq!(report["trust_summary"]["sorry_terms_minted"], 0, "{report}");
        assert_eq!(report["trust_summary"]["kernel_check_failures"], 0, "{report}");
        if accepted {
            assert_eq!(report["status"], "pass", "{report}");
            assert_eq!(report["success_count"], 4, "{report}");
            assert_eq!(report["failed_count"], 0, "{report}");
            assert_eq!(report["diverged_count"], 0, "{report}");
            for field in [
                "errors", "parser_recovery", "kernel_failures", "trust_failures", "diverged", "assumptions",
            ] {
                assert!(report[field].as_array().expect("verdict array").is_empty(), "{report}");
            }
        } else {
            assert_eq!(report["failed_count"], 1, "{report}");
            let errors = report["errors"].to_string();
            assert!(errors.contains("g12_twin"), "{report}");
            assert!(errors.contains("unsolved goals"), "{report}");
        }
    }
}

#[test]
fn nat_abs_borrowed_domain_runs_with_signed_runtime_inputs() {
    let dir = tempfile::tempdir().expect("temporary project");
    let file = dir.path().join("NatAbs.lean");
    // The argument count is known only at runtime: native lowering must
    // consume the Int.natAbs declaration rather than fold a closed literal.
    std::fs::write(
        &file,
        concat!(
            "def absValue (z : Int) : Nat := Int.natAbs z\n",
            "def main (args : List String) : IO Unit := do\n",
            "  IO.println (toString (absValue (Int.ofNat args.length)))\n",
            "  IO.println (toString (absValue (Int.negSucc args.length)))\n",
        ),
    )
    .expect("write source");
    for (args, expected) in [(&[][..], "0\n1\n"), (&["a", "b"][..], "2\n3\n")] {
        let output = Command::new(env!("CARGO_BIN_EXE_clean"))
            .args(["run", "--decl", "main"])
            .arg(&file)
            .arg("--")
            .args(args)
            .output()
            .expect("run clean native compiler");
        assert!(
            output.status.success(),
            "stdout={}\nstderr={}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(output.stdout, expected.as_bytes());
    }
}
