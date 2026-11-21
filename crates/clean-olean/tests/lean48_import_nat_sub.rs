// SPDX-License-Identifier: Apache-2.0

//! An ordinary Lean 4.8 consumer of a compiled `n - 1` definition reaches
//! Nat.sub over Clean's import-mode prelude. Exercise the same admission
//! gate and compare the loaded definition with the native fold's arithmetic
//! reference on that exact environment.

use std::collections::BTreeSet;
use std::fs;
use std::process::Command;

use clean_kernel::env::{native_fold_review, Environment};
use clean_kernel::name::Name;
use clean_olean::recheck_closed::ClosedRecheckRefusal;
use clean_olean::{load_module_with_deps, ImportedConeGate};

#[allow(dead_code)]
#[path = "support/installed_lean.rs"]
mod installed_lean;

#[test]
fn lean48_imported_nat_sub_reports_its_unqualified_definition() {
    let lean = installed_lean::installed_lean("leanprover/lean4:v4.8.0")
        .expect("this check requires the official Lean v4.8.0 library");
    let fixture = tempfile::tempdir().expect("subtraction fixture");
    // Compile the producer in the minimum library. The consumer retains its
    // ordinary implicit prelude. Its citation was refused at Nat.sub.
    for (module, source) in [
        ("Delta", "prelude\nimport Init.Prelude\n\ndef cut (n : Nat) : Nat := Nat.sub n (Nat.succ Nat.zero)\n"),
        ("UseDelta", "import Delta\n\ntheorem cutTwo : Eq (cut (Nat.succ (Nat.succ Nat.zero))) (Nat.succ Nat.zero) := Eq.refl _\n"),
    ] {
        let input = format!("{module}.lean");
        fs::write(fixture.path().join(&input), source).expect("write source");
        let checked = Command::new(&lean.bin)
            .current_dir(fixture.path())
            .env("LEAN_PATH", fixture.path())
            .args(["-o", &format!("{module}.olean"), &input])
            .output()
            .expect("run Lean 4.8");
        assert!(checked.status.success(), "{checked:?}");
    }
    let mut env = Environment::try_with_prelude_for_import().expect("import-mode prelude");
    clean_olean::declare_environment_world(&mut env, "v4.8.0")
        .expect("select the consumer's source and artifact world");
    let key = Name::from_string("Nat.sub");
    assert!(
        env.get_const(&key).is_none(),
        "the fixture must exercise an imported definition"
    );
    let mut gate = ImportedConeGate::new(&env);
    let roots = [fixture.path().to_path_buf(), lean.lib];
    load_module_with_deps(&mut env, "UseDelta", &roots).expect("load the checked fixture");
    let review = native_fold_review::review(&env, &key, true);
    assert!(
        review.fired > 0 && review.fired == review.cases,
        "{review:#?}"
    );
    assert_eq!(
        review.unanswered, 0,
        "every test case needs an independent answer"
    );
    let verdict = gate.check(&env, &BTreeSet::from([Name::from_string("cutTwo")]));
    assert!(verdict.untrusted_in_cone.iter().any(|n| n == "Nat.sub"));
    if review.passed() {
        assert!(verdict.passed(false), "{}", verdict.refusal_summary(false));
    } else {
        assert!(
            !verdict.passed(false),
            "unqualified mixed definition received credit"
        );
        let found = verdict
            .refusals
            .iter()
            .find_map(|refusal| match refusal {
                ClosedRecheckRefusal::ExtensionBindingMismatch { name, found, .. }
                    if name == "Nat.sub" =>
                {
                    Some(found)
                }
                _ => None,
            })
            .expect("the refused import must identify the subtraction dependency");
        assert_eq!(found.len(), 64);
        assert!(verdict
            .refusal_summary(false)
            .contains(&format!("observed dependency-closure fingerprint {found}")));
    }
}
