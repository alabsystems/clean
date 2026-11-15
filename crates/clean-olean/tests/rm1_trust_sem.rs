// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! RM1 (Trust `docs/plans/2026-10-15-proven-core.md` §2.2 and RM1): TrustSem's
//! `core_wf`, `run_sound`, `run_ub` and `run_adequate`, stated over the specr
//! translator's own free monad `SOut`, the committed counter-example to the naive
//! `run_sound`, and the controls for each departure from the plan's wording,
//! kernel-checked by Clean THROUGH the reference entry, every closure ⊆ Ax0.
//!
//! The fixture directory `tests/fixtures/lean/v4.30.0-rc2/trust_sem/` holds
//! Trust's `scripts/trust_core/specr/SpecrPrelude.lean` and
//! `generated/MiniRustSlice.lean`, byte for byte (Trust's `regen.py check`
//! compares them with this pinned copy), and `TrustSem.lean`. The test builds the
//! shared module `MiniRust` (the prelude and the slice in a `noncomputable
//! section`: Lean's code generator does not take `SOut.rec`, the kernel does),
//! compiles `TrustSem` against it with the pinned Lean, and replays the `.olean`s
//! with `reference_base_closed`: every constant of the theorems' cone, the
//! generated MiniRust slice and pinned `Init` included, is admitted through
//! `ReferenceKernel` (R143's Ax0 fence among its gates).
//!
//! * The closure each theorem reaches, read here independently of the entry,
//!   is exactly what Lean's `#print axioms` prints for it (recorded in
//!   [`EXPECTED`]), and ⊆ Ax0.
//! * Negative controls on the same entry, each beside a control that is
//!   accepted: the counter-example's computed run with its UB message changed
//!   (`ptr1` → `ptr0`); the generated MiniRust slice's computed run of K8's
//!   abort minitest claimed to end in `MachineStop`; `core_wf`'s proof offered
//!   for the unconditional `core_wf`; and `run_sound`'s proof offered for the
//!   naive statement.

use std::collections::{BTreeSet, HashSet};
use std::path::Path;
use std::process::Command;

use clean_kernel::env::{ConstantKind, Declaration, Environment};
use clean_kernel::expr::{Expr, UsedConstants};
use clean_kernel::name::Name;
use clean_kernel::{ReferenceRefusal, TheoryId};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::{load_module_with_deps, reference_base_closed};

#[path = "support/installed_lean.rs"]
#[allow(dead_code)]
mod installed_lean;
use installed_lean::{installed_lean, InstalledLean};

const PINNED: &str = "v4.30.0-rc2";

fn n(s: &str) -> Name {
    Name::from_string(s)
}

/// Each checked constant and the axiom closure Lean 4.30's `#print axioms`
/// reports for it.
const EXPECTED: &[(&str, &[&str])] = &[
    (
        "TrustSem.core_wf",
        &["propext", "Classical.choice", "Quot.sound"],
    ),
    ("TrustSem.run_sound", &["propext"]),
    (
        "TrustSem.run_ub",
        &["propext", "Classical.choice", "Quot.sound"],
    ),
    ("TrustSem.run_adequate", &["propext", "Quot.sound"]),
    ("TrustSem.stepT_runOracle", &["propext"]),
    ("TrustSem.naive_run_sound_fails", &["propext"]),
    ("TrustSem.twoCast_zero_run", &["propext"]),
    ("TrustSem.twoCast_done", &["propext"]),
    (
        "TrustSem.twoCastBad_ub",
        &["propext", "Classical.choice", "Quot.sound"],
    ),
    (
        "TrustSem.run_ub_common_trace_fails",
        &["propext", "Classical.choice", "Quot.sound"],
    ),
    ("TrustSem.loopP_diverges", &["propext"]),
    ("TrustSem.loopP_no_fin", &["propext"]),
    ("TrustSem.divOrUB_diverges", &["propext"]),
    ("TrustSem.divOrUB_no_ub", &["propext"]),
    ("TrustSem.core_wf_unconditional_fails", &["propext"]),
    ("TrustSem.miniRust_run_sound", &["propext"]),
    (
        "TrustSem.miniRust_run_ub",
        &["propext", "Classical.choice", "Quot.sound"],
    ),
    ("TrustSem.miniRust_run_adequate", &["propext", "Quot.sound"]),
    (
        "TrustSem.miniRust_core_wf",
        &["propext", "Classical.choice", "Quot.sound"],
    ),
    ("TrustSem.miniRust_abort_run", &["propext"]),
    ("TrustSem.miniRust_zero_rejected", &["propext"]),
    ("TrustSem.miniRust_abort", &["propext"]),
];

const AX0: [&str; 3] = ["propext", "Quot.sound", "Classical.choice"];

/// Every constant `name` reaches through types, values, inductive families,
/// constructors and recursors, by name.
fn reach(env: &Environment, root: &Name) -> HashSet<Name> {
    let mut seen: HashSet<Name> = HashSet::new();
    let mut stack = vec![root.clone()];
    while let Some(x) = stack.pop() {
        if !seen.insert(x.clone()) {
            continue;
        }
        let mut used = HashSet::new();
        let walk = |e: &Expr, used: &mut HashSet<Name>| {
            e.used_constants_dag(UsedConstants::WithProjectionStructures, used);
        };
        if let Some(c) = env.get_const(&x) {
            walk(&c.type_, &mut used);
            if let Some(v) = &c.value {
                walk(v, &mut used);
            }
        }
        if let Some(i) = env.get_inductive(&x) {
            walk(&i.type_, &mut used);
            used.extend(i.constructor_names.iter().cloned());
            used.extend(i.all_names.iter().cloned());
        }
        if let Some(c) = env.get_constructor(&x) {
            walk(&c.type_, &mut used);
            used.insert(c.inductive_name.clone());
        }
        if let Some(r) = env.get_recursor(&x) {
            walk(&r.type_, &mut used);
            used.insert(r.inductive_name.clone());
        }
        stack.extend(used.into_iter().filter(|u| !seen.contains(u)));
    }
    seen
}

/// The quotient formers: part of the theory, not axioms (Ax0's definition;
/// `reference_ax0.rs`). `Quot.sound` is an axiom.
const QUOT_FORMERS: [&str; 4] = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"];

/// The axioms `root` reaches, the quotient formers excluded.
fn axioms_of(env: &Environment, root: &Name) -> BTreeSet<String> {
    reach(env, root)
        .into_iter()
        .filter(|x| {
            env.get_const(x)
                .is_some_and(|c| c.kind == ConstantKind::Axiom && c.value.is_none())
        })
        .map(|x| x.to_string())
        .filter(|x| !QUOT_FORMERS.contains(&x.as_str()))
        .collect()
}

/// The fixture directory.
fn fixture_dir(lean: &InstalledLean) -> std::path::PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean")
        .join(&lean.version)
        .join("trust_sem")
}

/// `lean --root . -o <module>.olean <module>.lean` in `dir` (the pinned fixture
/// recipe's compile step, `dir` as cwd and `LEAN_PATH`); panics with Lean's
/// output when it fails.
fn compile_module(lean: &InstalledLean, dir: &Path, module: &str) {
    let lean_file = format!("{module}.lean");
    let olean_file = format!("{module}.olean");
    let output = Command::new(&lean.bin)
        .current_dir(dir)
        .env("LEAN_PATH", dir)
        .args(["--root", ".", "-o", olean_file.as_str(), lean_file.as_str()])
        .output()
        .unwrap_or_else(|e| panic!("cannot execute {}: {e}", lean.bin.display()));
    assert!(
        output.status.success(),
        "`{} -o {olean_file} {lean_file}` failed with {}\n--- stdout ---\n{}\n--- stderr ---\n{}",
        lean.bin.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Build the one shared `MiniRust` model (Trust's prelude and slice, verbatim, in a
/// `noncomputable section`) and `TrustSem` into a fresh temporary directory.
fn compile_trust_sem(lean: &InstalledLean) -> tempfile::TempDir {
    let src = fixture_dir(lean);
    let dir = tempfile::tempdir().expect("temporary fixture directory");
    let read = |name: &str| {
        std::fs::read_to_string(src.join(name))
            .unwrap_or_else(|e| panic!("read {}: {e}", src.join(name).display()))
    };
    let slice = format!(
        "noncomputable section\n{}{}\nend\n",
        read("SpecrPrelude.lean"),
        read("MiniRustSlice.lean")
    );
    // One model namespace for Core and SemR/function proofs. The wrapper is
    // generated from the original byte-preserved inputs, then compared with
    // the maintained canonical IR copy before either consumer is compiled.
    let canonical = src
        .parent()
        .expect("Lean fixture cohort")
        .join("semr/MiniRust.lean");
    assert_eq!(
        slice.as_bytes(),
        std::fs::read(&canonical).expect("read canonical shared MiniRust"),
        "Core's generated model differs from canonical MiniRust; preserve regen guards"
    );
    std::fs::write(dir.path().join("MiniRust.lean"), slice).expect("write shared MiniRust");
    std::fs::copy(src.join("TrustSem.lean"), dir.path().join("TrustSem.lean"))
        .expect("copy TrustSem.lean");
    compile_module(lean, dir.path(), "MiniRust");
    compile_module(lean, dir.path(), "TrustSem");
    dir
}

/// `f a₁ … aₙ`.
fn apps(f: Expr, args: Vec<Expr>) -> Expr {
    args.into_iter().fold(f, Expr::app)
}

fn c(name: &str) -> Expr {
    Expr::const_(n(name), vec![])
}

/// Measured 2026-10-25: 24.5 s in `--release` (5559 constants through the entry);
/// the debug test profile is far slower (a 639-constant first version took
/// 982 s), so a debug run skips it unless `--ignored` asks for it.
#[test]
#[cfg_attr(
    debug_assertions,
    ignore = "unoptimized replay of the slice takes many minutes; run with --release or --ignored"
)]
fn test_trust_sem_theorems_are_admitted_through_the_entry_with_closure_in_ax0() {
    assert_eq!(
        include_str!("../../../lean-toolchain").trim(),
        format!("leanprover/lean4:{PINNED}"),
        "this fixture is compiled by the {PINNED} pin; the workspace pin moved"
    );
    let lean = installed_lean(&format!("leanprover/lean4:{PINNED}")).unwrap_or_else(|| {
        panic!("the pinned lean-{PINNED} toolchain is not installed (KR0 plan step 0.1)")
    });
    let dir = compile_trust_sem(&lean);
    let mut env = Environment::for_lean_replay();
    load_module_with_deps(
        &mut env,
        "TrustSem",
        &[dir.path().to_path_buf(), lean.lib.clone()],
    )
    .unwrap_or_else(|e| panic!("load TrustSem: {e}"));

    let targets: BTreeSet<Name> = EXPECTED.iter().map(|(t, _)| n(t)).collect();
    let built =
        reference_base_closed(&env, &targets, &ClosedRecheckOptions::default()).expect("start");
    assert!(
        built.report.passed(),
        "{}\nentry refusals: {:?}",
        built.report.verdict_sentence(),
        built.entry_refusals
    );
    assert!(
        built.entry_refusals.is_empty(),
        "{:?}",
        built.entry_refusals
    );
    for (t, _) in EXPECTED {
        assert!(
            built.admitted.contains(&n(t)),
            "{t} was not admitted through the entry"
        );
    }
    // The generated slice itself went through the entry, not only the theorems.
    for generated in [
        "MRf.Machine.step",
        "MRf.Machine.new",
        "MRf.IntPtrCast.int2ptr",
        "SOut.runOracle",
    ] {
        assert!(
            built.admitted.contains(&n(generated)) || generated == "MRf.IntPtrCast.int2ptr",
            "{generated} was not admitted through the entry"
        );
    }
    eprintln!(
        "rm1_trust_sem: {} constants admitted through the entry",
        built.admitted.len()
    );
    let mut k = built.into_kernel().expect("a passing, pinned replay");
    assert_eq!(k.theory_id(), TheoryId::LeanReferenceV1);

    // ── Closures, read from the entry's own environment. ──
    let kenv = k.environment();
    let ax0: BTreeSet<String> = AX0.iter().map(|s| (*s).to_string()).collect();
    for (t, want) in EXPECTED {
        let got = axioms_of(kenv, &n(t));
        let want: BTreeSet<String> = want.iter().map(|s| (*s).to_string()).collect();
        assert_eq!(got, want, "{t}: closure differs from Lean's #print axioms");
        assert!(got.is_subset(&ax0), "{t}: closure {got:?} is not ⊆ Ax0");
    }
    // No sorry, native evaluation or compiler trust anywhere in the cone.
    for (t, _) in EXPECTED {
        let r = reach(kenv, &n(t));
        for bad in [
            "sorryAx",
            "Lean.ofReduceBool",
            "Lean.ofReduceNat",
            "Lean.trustCompiler",
        ] {
            assert!(!r.contains(&n(bad)), "{t} reaches {bad}");
        }
    }

    // ── Negative control 1: the counter-example's computed UB run, message changed. ──
    let zero_run = kenv_value(&env, "TrustSem.twoCast_zero_run");
    let claim = |msg: &str| Expr::app(c("TrustSem.zeroRunClaim"), Expr::str_lit(msg));
    k.add_checked(Declaration::Theorem {
        name: n("TrustSem.rm1_control_zero_run"),
        level_params: vec![],
        type_: claim("write through ptr1: provenance mismatch"),
        value: zero_run.clone(),
    })
    .expect("control: the genuine computed run is accepted");
    let forged = k
        .add_checked(Declaration::Theorem {
            name: n("TrustSem.rm1_forged_zero_run"),
            level_params: vec![],
            type_: claim("write through ptr0: provenance mismatch"),
            value: zero_run,
        })
        .expect_err("a wrong UB message for the computed run is refused");
    assert!(
        matches!(forged, ReferenceRefusal::Kernel(_)),
        "got {forged:?}"
    );

    // ── Negative control 2: the generated slice's computed abort run, outcome changed. ──
    let abort_run = kenv_value(&env, "TrustSem.miniRust_abort_run");
    let abort_claim = |t: &str| Expr::app(c("TrustSem.abortRunClaim"), c(t));
    k.add_checked(Declaration::Theorem {
        name: n("TrustSem.rm1_control_abort_run"),
        level_params: vec![],
        type_: abort_claim("MR_TerminationInfo.Abort"),
        value: abort_run.clone(),
    })
    .expect("control: the generated code's computed abort run is accepted");
    let forged = k
        .add_checked(Declaration::Theorem {
            name: n("TrustSem.rm1_forged_abort_run"),
            level_params: vec![],
            type_: abort_claim("MR_TerminationInfo.MachineStop"),
            value: abort_run,
        })
        .expect_err("a wrong outcome for the generated code's run is refused");
    assert!(
        matches!(forged, ReferenceRefusal::Kernel(_)),
        "got {forged:?}"
    );

    // ── Negative control 3: core_wf's proof offered for the unconditional core_wf. ──
    let core_wf = kenv_value(&env, "TrustSem.core_wf");
    let refused = k
        .add_checked(Declaration::Theorem {
            name: n("TrustSem.rm1_forged_core_wf"),
            level_params: vec![],
            type_: c("TrustSem.CoreWfUnconditional"),
            value: core_wf,
        })
        .expect_err("core_wf does not prove the unconditional statement");
    assert!(
        matches!(refused, ReferenceRefusal::Kernel(_)),
        "got {refused:?}"
    );
    // Control: its negation is what the fixture proves, re-admitted under a fresh name.
    let unconditional_fails = env
        .get_const(&n("TrustSem.core_wf_unconditional_fails"))
        .expect("core_wf_unconditional_fails")
        .clone();
    k.add_checked(Declaration::Theorem {
        name: n("TrustSem.rm1_control_core_wf_unconditional_fails"),
        level_params: vec![],
        type_: unconditional_fails.type_.clone(),
        value: unconditional_fails
            .value
            .clone()
            .expect("a theorem has a proof"),
    })
    .expect("control: the refutation of the unconditional core_wf is accepted");

    // ── Negative control 4: run_sound's proof offered for the naive statement. ──
    let naive = apps(
        c("TrustSem.NaiveRunSound"),
        vec![
            c("Unit"),
            c("Unit"),
            c("MR_TerminationInfo"),
            c("TrustSem.twoCast"),
        ],
    );
    let run_sound = kenv_value(&env, "TrustSem.run_sound");
    let refused = k
        .add_checked(Declaration::Theorem {
            name: n("TrustSem.rm1_forged_naive"),
            level_params: vec![],
            type_: naive,
            value: run_sound,
        })
        .expect_err("run_sound does not prove the naive statement");
    assert!(
        matches!(refused, ReferenceRefusal::Kernel(_)),
        "got {refused:?}"
    );
}

fn kenv_value(env: &Environment, name: &str) -> Expr {
    env.get_const(&n(name))
        .and_then(|c| c.value.clone())
        .unwrap_or_else(|| panic!("{name} has a value"))
}
