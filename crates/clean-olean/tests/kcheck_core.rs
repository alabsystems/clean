// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Plan unit C2 (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`): the
//! advice-replaying checker `theories/kcheck`, compiled by pinned Lean over
//! `theories/cic_l`, replayed by `leanchecker --fresh`, and re-admitted
//! constant by constant through Clean's reference kernel from an empty base.
//!
//! What a green run shows: every constant the checker's fifteen modules
//! declare is admitted by two kernels; no soundness lemma depends on an axiom
//! outside the committed closure; each lemma proves the statement pinned for
//! it and not `False`, a weakened statement, or the acceptance of a run the
//! checker refuses. What it does not show: semantic soundness (unit C3). The
//! lemmas relate the checker to the declarative judgment of `theories/cic_l`
//! under the typing premises `theories/kcheck/README.md` lists.
//!
//! A statement pin is the meaning digest (`support/meaning_digest.rs`) of a
//! proposition definition in `KCheck.Contracts`: the definition and every
//! definition, inductive and compiler auxiliary of the package it reaches,
//! down to Init, so a pin moves when the checker or the judgment a statement
//! names is redefined. The package is the theories the fixture family
//! `kcheck_core` compiles, `cic_l` and `kcheck`. Re-pin with
//! `CLEAN_REPIN_STATEMENT_PINS=1 scripts/heavy_gate.sh run 16 kcheck-core-repin --
//! "$(rustup run trust rustc --print sysroot)/bin/targo" --unverified test -p
//! clean-olean --locked --test kcheck_core`: the run rewrites
//! `theories/kcheck/statement_pins.json` and still fails, and the next run
//! without the variable confirms it.

#[path = "support/meaning_digest.rs"]
mod meaning_digest;

use std::collections::{BTreeMap, BTreeSet};
use std::process::Command;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{Expr, ExprKind, KernelEnvError, KernelTypeError, Name, ReferenceRefusal};
use clean_olean::recheck_closed::ClosedRecheckOptions;
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::{
    load_module_with_deps, read_artifact, reference_base_closed, require_pinned_lean_lib_path,
    ArtifactDepth,
};
use meaning_digest::{MeaningDigests, Package};

/// The module that imports every other module of the package.
const ROOT: &str = "KCheck.Contracts";

/// `(soundness lemma, statement pin in KCheck.Contracts)`.
const CONTRACTS: &[(&str, &str)] = &[
    ("levelEq_sound", "levelComparison"),
    ("eq_of_exprBeq", "syntacticEquality"),
    ("exprClosed_sound", "closedTerms"),
    ("exprLevelScoped_sound", "scopedTerms"),
    ("headStep_sound", "headStep"),
    ("replayHead_sound", "headScript"),
    ("replayHead_convert", "typeReduction"),
    ("sort_inversion", "sortInversion"),
    ("checkDefEq_sound", "definitionalEquality"),
    ("checkDefEq_convert", "typeConversion"),
    ("inferLeaf_sound", "leafInference"),
    ("infer_sound", "inference"),
    ("infer_sound_direct", "directInference"),
    ("checkDecl_sound", "declaration"),
    ("checkDecls_wellFormed", "environment"),
    ("checkDecls_wellFormed_direct", "directEnvironment"),
];

/// `(real proof, statement nobody proves)`: a soundness lemma offered at its
/// own statement with a premise removed or the conclusion changed.
const FORGED_STATEMENTS: &[(&str, &str)] = &[
    ("checkDefEq_sound", "forged_definitionalEquality"),
    ("headStep_sound", "forged_headStep"),
    ("infer_sound_direct", "forged_directInference"),
    ("levelEq_sound", "forged_levelComparison"),
    ("checkDecls_wellFormed_direct", "forged_directEnvironment"),
    ("checkDecl_sound", "forged_declaration"),
];

/// `(accepted case, acceptance claimed for the refused twin)`. The proof is the
/// accepted case's `rfl`; admitting it at the twin would need the reference
/// kernel to evaluate the checker to `ok` on a run it refuses.
const FORGED_RUNS: &[(&str, &str)] = &[
    ("beta_accepted", "forged_beta_false"),
    ("beta_accepted", "forged_beta_no_redex"),
    ("identity_accepted", "forged_identity_open"),
    ("environment_accepted", "forged_environment_order"),
    ("definition_in_type_accepted", "forged_theorem_not_prop"),
    ("argument_in_scope_accepted", "forged_argument_out_of_scope"),
    ("polymorphic_zero_accepted", "forged_arity_missing"),
    ("proof_irrelevance_accepted", "forged_proof_irrelevance"),
    ("application_accepted", "forged_application"),
    ("delta_accepted", "forged_delta_opaque"),
    ("eta_accepted", "forged_eta"),
    ("environment_accepted", "forged_wrong_value_type"),
    ("let_accepted", "forged_let"),
];

fn name(s: &str) -> Name {
    Name::from_string(s)
}

/// The module stems of `theories/kcheck/ORDER`.
fn order_stems() -> Vec<&'static str> {
    include_str!("../../../theories/kcheck/ORDER")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty() && !line.starts_with('#'))
        .collect()
}

fn is_type_mismatch<T>(result: &Result<T, ReferenceRefusal>) -> bool {
    matches!(
        result,
        Err(ReferenceRefusal::Kernel(KernelEnvError::TypeCheckFailed {
            source: KernelTypeError::TypeMismatch { .. },
            ..
        }))
    )
}

#[test]
fn kcheck_core_rechecks_through_two_kernels_with_forged_controls() {
    let lib = require_pinned_lean_lib_path().expect("install the repository-pinned Lean toolchain");
    let compiled = compiled_fixture_dir("kcheck_core");
    let lean = clean_olean::pinned_lean_binary().expect("pinned Lean binary");
    let bin = lean.parent().expect("Lean bin directory");
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));

    // Kernel one: Lean's own, replaying the root module and everything below
    // it from nothing.
    let independent = Command::new(bin.join("leanchecker"))
        .args(["--fresh", ROOT])
        .current_dir(&compiled)
        .env(
            "LEAN_PATH",
            std::env::join_paths([&compiled, &lib]).expect("Lean path"),
        )
        .env("PATH", std::env::join_paths(paths).expect("binary path"))
        .output()
        .expect("run pinned independent Lean kernel");
    assert!(
        independent.status.success(),
        "leanchecker --fresh {ROOT} failed: {}\n{}",
        String::from_utf8_lossy(&independent.stdout),
        String::from_utf8_lossy(&independent.stderr)
    );

    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(&mut loaded, ROOT, &[compiled.clone(), lib])
        .expect("load the compiled checker");
    let package = Package::of_fixture(&compiled, "kcheck_core", &["cic_l", "kcheck"]);

    // The subjects are the constants the package's own modules declare, read
    // from each artifact's name table: no name prefix decides membership, so
    // a private helper or a generated auxiliary cannot fall outside the set,
    // and a `CICL.*` constant cannot be counted as the checker's.
    //
    // One class of name is in a table and is no subject: the `unsafe` copy
    // `<definition>._unsafe_rec` Lean's compiler stores beside a structurally
    // recursive definition. The artifact itself marks it unsafe, Lean's replay
    // never admits it and no safe declaration may use it. Each must be marked
    // so by its own artifact, and its definition must be a subject.
    let stems = order_stems();
    assert_eq!(
        stems.len(),
        15,
        "module denominator of theories/kcheck/ORDER"
    );
    // Names the loader left out because the artifact that declares them marks
    // them `unsafe` or `partial`. A constant name has one declaring module in
    // a load, so membership here is a fact about that name's own artifact.
    let not_replayable: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|summary| summary.skipped_not_replayable.iter().map(String::as_str))
        .collect();
    let mut targets: BTreeSet<Name> = BTreeSet::new();
    let mut compiler_copies: BTreeSet<String> = BTreeSet::new();
    for stem in &stems {
        let module = stem.replace('/', ".");
        let artifact = read_artifact(
            &module,
            &compiled.join(format!("{stem}.olean")),
            ArtifactDepth::Names,
        )
        .unwrap_or_else(|error| panic!("read {module}: {error}"));
        assert!(!artifact.names.is_empty(), "{module} declares nothing");
        let mut copies = 0_usize;
        for constant in &artifact.names {
            let text = constant.to_string();
            if loaded.get_const(constant).is_none() {
                assert!(
                    text.ends_with("._unsafe_rec") && not_replayable.contains(text.as_str()),
                    "{module} declares {constant}, which the load did not make resident and \
                     the artifact does not mark as a compiler's unsafe copy"
                );
                assert!(compiler_copies.insert(text), "{constant} is declared twice");
                copies += 1;
                continue;
            }
            assert!(
                !loaded.is_unsafe(constant) && !loaded.is_partial(constant),
                "{module} declares {constant} unsafe or partial"
            );
            assert!(
                targets.insert(constant.clone()),
                "{constant} is declared by two modules"
            );
        }
        eprintln!(
            "module {module}: {} constants, {copies} unsafe compiler copies",
            artifact.names.len()
        );
    }
    for copy in &compiler_copies {
        let definition = copy
            .strip_suffix("._unsafe_rec")
            .expect("checked when collected");
        assert!(
            targets.contains(&name(definition)),
            "{copy} has no definition among the subjects"
        );
    }

    // Kernel two: Clean's reference kernel, from an empty base. Loading above
    // is parsing, never evidence of admission.
    let checked = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("construct dependency-closed reference replay");
    assert!(
        checked.report.passed() && checked.entry_refusals.is_empty(),
        "{}\n{:?}",
        checked.report.verdict_sentence(),
        checked.entry_refusals
    );
    let mut kernel = checked
        .into_kernel()
        .expect("all reference admissions passed");

    // The case denominator: every case of KCheck/Cases.lean is a re-admitted
    // theorem, and the executable's committed output names the same cases
    // with the same verdicts.
    // A case `c` is the theorem `c_accepted : run_c = Except.ok _` or
    // `c_refused : run_c = Except.error _`; the verdict is read from the
    // theorem's statement, the name only locates it.
    let case_states = |case: &str, accepted: bool| -> bool {
        let suffix = if accepted { "accepted" } else { "refused" };
        let theorem = name(&format!("KCheck.Cases.{case}_{suffix}"));
        let Some(constant) = loaded.get_const(&theorem) else {
            return false;
        };
        let statement = &constant.type_;
        let is_const = |e: &Expr, expected: &str| matches!(e.get_app_fn().kind(), ExprKind::Const(n, _) if n == &name(expected));
        let verdict = if accepted {
            "Except.ok"
        } else {
            "Except.error"
        };
        let run = name(&format!("KCheck.Cases.run_{case}"));
        let mut sides = statement.get_app_args_iter();
        targets.contains(&theorem)
            && targets.contains(&run)
            && constant.value.is_some()
            && is_const(statement, "Eq")
            && statement.get_app_num_args() == 3
            && sides.next().is_some_and(|right| is_const(right, verdict))
            && sides
                .next()
                .is_some_and(|left| matches!(left.kind(), ExprKind::Const(n, _) if n == &run))
    };
    let expected_output = include_str!("../../../theories/kcheck/expected_output.txt");
    let mut accepted_cases = 0_usize;
    let mut refused_cases = 0_usize;
    let mut summary = None;
    for line in expected_output.lines() {
        if let Some(rest) = line.strip_prefix("cases ") {
            summary = Some(rest.to_owned());
            continue;
        }
        let (case, verdict) = line
            .split_once(": ")
            .unwrap_or_else(|| panic!("malformed verdict line: {line}"));
        let accepted = if verdict == "accepted" || verdict.starts_with("accepted ") {
            true
        } else if verdict.starts_with("refused ") {
            false
        } else {
            panic!("verdict line is neither accepted nor refused: {line}");
        };
        assert!(
            case_states(case, accepted),
            "no re-admitted theorem states the verdict of line: {line}"
        );
        if accepted {
            accepted_cases += 1;
        } else {
            refused_cases += 1;
        }
    }
    assert_eq!(
        (accepted_cases, refused_cases),
        (38, 63),
        "exact case denominator"
    );
    assert_eq!(
        summary.as_deref(),
        Some("101, accepted 38, refused 63"),
        "the executable's own count"
    );
    let runs = targets
        .iter()
        .filter(|c| {
            c.to_string()
                .strip_prefix("KCheck.Cases.run_")
                .is_some_and(|case| !case.contains('.'))
        })
        .count();
    assert_eq!(
        runs, 101,
        "every run of KCheck/Cases.lean has an output line"
    );

    // Axiom closure: each subject's observed closure, and the committed exact
    // closure of each soundness lemma. A lemma that starts to use
    // `Classical.choice`, or stops needing `Quot.sound`, fails here.
    let allowed: BTreeSet<String> = [
        "propext",
        "Quot.sound",
        "Quot",
        "Quot.mk",
        "Quot.lift",
        "Quot.ind",
    ]
    .into_iter()
    .map(str::to_owned)
    .collect();
    let closure_of = |env: &Environment, subject: &Name| -> BTreeSet<String> {
        let mut closure = env.axiom_deps(subject).expect("admitted declaration");
        closure.extend(env.foundational_axiom_deps(subject).expect("closure"));
        closure.iter().map(ToString::to_string).collect()
    };
    let mut union: BTreeSet<String> = BTreeSet::new();
    for subject in &targets {
        let closure = closure_of(kernel.environment(), subject);
        assert!(closure.is_subset(&allowed), "{subject}: {closure:?}");
        union.extend(closure);
    }
    let committed_closures: BTreeMap<String, BTreeSet<String>> =
        serde_json::from_str(include_str!("../../../theories/kcheck/axiom_closures.json"))
            .expect("committed axiom closures");
    let mut observed_closures: BTreeMap<String, BTreeSet<String>> = BTreeMap::new();
    observed_closures.insert("*".to_owned(), union);
    for (lemma, _) in CONTRACTS {
        let subject = name(&format!("KCheck.{lemma}"));
        assert!(targets.contains(&subject), "missing lemma {lemma}");
        observed_closures.insert(
            (*lemma).to_owned(),
            closure_of(kernel.environment(), &subject),
        );
    }
    for (subject, closure) in &observed_closures {
        eprintln!("axiom-closure {subject} {closure:?}");
    }

    // Statement pins. Every digest is printed before any is compared, so one
    // run of a changed statement set shows all of them.
    let committed_pins: BTreeMap<String, String> =
        serde_json::from_str(include_str!("../../../theories/kcheck/statement_pins.json"))
            .expect("committed statement pins");
    let statement = |pin: &str| -> Expr {
        loaded
            .get_const(&name(&format!("KCheck.Contracts.{pin}")))
            .unwrap_or_else(|| panic!("missing statement {pin}"))
            .value
            .clone()
            .unwrap_or_else(|| panic!("{pin} is not a proposition definition"))
    };
    let mut observed_pins: BTreeMap<String, String> = BTreeMap::new();
    {
        let digests = MeaningDigests::new(kernel.environment(), &package);
        let mut roots = Vec::new();
        for pin in CONTRACTS
            .iter()
            .chain(FORGED_STATEMENTS)
            .chain(FORGED_RUNS)
            .map(|(_, pin)| *pin)
        {
            let root = name(&format!("KCheck.Contracts.{pin}"));
            let digest = digests
                .digest(&root)
                .unwrap_or_else(|error| panic!("{error}"));
            assert!(
                observed_pins.insert(pin.to_owned(), digest).is_none(),
                "{pin} is listed twice"
            );
            roots.push(root);
        }
        for (pin, value) in &observed_pins {
            eprintln!("statement-pin {pin} {value}");
        }
        eprintln!(
            "{}",
            digests
                .describe(&package, &roots)
                .unwrap_or_else(|error| panic!("{error}"))
        );
    }
    assert_eq!(
        observed_pins.len(),
        35,
        "16 contracts, 6 forged statements, 13 forged runs"
    );
    assert_eq!(
        observed_closures, committed_closures,
        "observed axiom closures differ from theories/kcheck/axiom_closures.json"
    );
    if let Err(failure) = meaning_digest::check_pins(
        &observed_pins,
        &committed_pins,
        "theories/kcheck/statement_pins.json",
    ) {
        panic!("{failure}");
    }

    // Each lemma's own proof is admitted at the statement pinned for it, and
    // refused at `False`.
    for (lemma, pin) in CONTRACTS {
        let proof = loaded
            .get_const(&name(&format!("KCheck.{lemma}")))
            .expect("soundness lemma");
        let value = proof.value.clone().expect("the lemma has a proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheck.Controls.{pin}_positive")),
                level_params: proof.level_params.clone(),
                type_: statement(pin),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{lemma} at its pinned statement {pin}: {refusal:?}"));
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{pin}_false")),
            level_params: proof.level_params.clone(),
            type_: Expr::const_(name("False"), vec![]),
            value,
        });
        assert!(
            is_type_mismatch(&bad),
            "{lemma} at False must fail by type mismatch: {bad:?}"
        );
    }

    // A real proof is refused at a statement it does not prove.
    for (lemma, forged) in FORGED_STATEMENTS {
        let proof = loaded
            .get_const(&name(&format!("KCheck.{lemma}")))
            .expect("soundness lemma");
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{forged}")),
            level_params: proof.level_params.clone(),
            type_: statement(forged),
            value: proof.value.clone().expect("the lemma has a proof"),
        });
        assert!(
            is_type_mismatch(&bad),
            "{lemma} at {forged} must fail by type mismatch: {bad:?}"
        );
    }

    // An accepted run's proof is admitted at its own statement and refused at
    // the acceptance of its refused twin: the reference kernel evaluates the
    // checker on both.
    for (case, forged) in FORGED_RUNS {
        let proof = loaded
            .get_const(&name(&format!("KCheck.Cases.{case}")))
            .expect("accepted case");
        let value = proof.value.clone().expect("the case has a proof");
        kernel
            .add_checked(Declaration::Theorem {
                name: name(&format!("KCheck.Controls.{forged}_own_statement")),
                level_params: proof.level_params.clone(),
                type_: proof.type_.clone(),
                value: value.clone(),
            })
            .unwrap_or_else(|refusal| panic!("{case} at its own statement: {refusal:?}"));
        let bad = kernel.add_checked(Declaration::Theorem {
            name: name(&format!("KCheck.Controls.{forged}")),
            level_params: proof.level_params.clone(),
            type_: statement(forged),
            value,
        });
        assert!(
            is_type_mismatch(&bad),
            "{case} at {forged} must fail by type mismatch: {bad:?}"
        );
    }

    eprintln!(
        "kcheck subjects {}, modules {}, cases {} ({accepted_cases} accepted, {refused_cases} \
         refused), contracts {}, forged statements {}, forged runs {}",
        targets.len(),
        stems.len(),
        accepted_cases + refused_cases,
        CONTRACTS.len(),
        FORGED_STATEMENTS.len(),
        FORGED_RUNS.len()
    );
}
