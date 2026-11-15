// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The patched-kernel control at Clean's `.olean` and export re-check lanes
//! (unit P3 of `docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md`; the
//! two-leg contract is in clean-kernel's `tests/support/patched_kernel_control.rs`).
//!
//! The planted module is `P3Planted.olean` (fixture family `p3_planted`):
//! `theorem planted : False := Nat.zero`, written by the pinned Lean with its
//! kernel check skipped. The same bytes go to every Clean lane that re-checks an
//! `.olean` and to the pinned `leanchecker --fresh`, Lean's own kernel. The
//! NDJSON front door gets the same declaration in Lean's export format.

#[path = "../../clean-kernel/tests/support/patched_kernel_control.rs"]
mod control;

use std::collections::{BTreeMap, BTreeSet, HashSet};
use std::io::Cursor;
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_kernel::env::{ConstantInfo, Environment, ProofValueElision, TrustedEnvExt};
use clean_kernel::name::Name;
use clean_kernel::tc::DEFAULT_HEARTBEAT_LIMIT;
use clean_olean::ndjson::{check_export_reader, DeclarationVerdict, ExitClass, ExportCheckOptions};
use clean_olean::test_support::compiled_fixture_dir;
use clean_olean::verify_batch::{
    collect_new_env_names, verify_one_module_with_mode_in_run, ValidationMode,
};
use clean_olean::verify_batch_full::{
    typecheck_constants_full, typecheck_constants_full_streaming,
};
use clean_olean::verify_parallel::typecheck_constants_full_parallel;
use clean_olean::{
    convert_parsed_constant_to_const_info, default_search_paths,
    load_module_with_deps_shared_with_policy, parse_module_file, ClosedRecheckRefusal,
    ImportedConeGate, OleanImportPolicy,
};
use control::{by, Observed, Outcome, Pin};

const PACKAGE: &str = "clean-olean";
const FAMILY: &str = "p3_planted";
const PLANTED: &str = "planted";
const HONEST: &str = "p3_honest";

const LANE_MISMATCH: &str = "refused: TypeMismatch";
const LANE_MINT: &str = "counted kernel-verified (pass 1, fail 0)";

const PINS: &[Pin] = &[
    Pin {
        site: "olean.typecheck_constants_full",
        mints: "a pass count for the target: the eager lane of `clean olean verify-batch --full-validation` and of mathverse per-constant-verify",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, LANE_MISMATCH),
        mutant: Outcome::minted(LANE_MINT),
    },
    Pin {
        site: "olean.typecheck_constants_full_parallel",
        mints: "a pass count for the target from the parallel lane",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, LANE_MISMATCH),
        mutant: Outcome::minted(LANE_MINT),
    },
    Pin {
        site: "olean.typecheck_constants_full_streaming",
        mints: "a pass count for the target from the streaming lane with proof-value elision",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, LANE_MISMATCH),
        mutant: Outcome::minted(LANE_MINT),
    },
    Pin {
        site: "olean.verify_one_module_in_run",
        mints: "ModuleResult.tc_pass for the module, the per-module row of `clean olean verify-batch --full-validation`",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "tc_fail 1: TypeMismatch"),
        mutant: Outcome::minted("tc_pass 1, tc_fail 0"),
    },
    Pin {
        site: "olean.ndjson.check_export_reader",
        mints: "ExitClass::Accept (exit 0) from the NDJSON front door (`clean olean replay --from-export`, `clean_export_check`)",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "ExitClass::Reject, first refusal `planted`: TypeMismatch"),
        mutant: Outcome::minted("ExitClass::Accept, `planted` admitted"),
    },
    Pin {
        site: "olean.imported_cone_gate",
        mints: "ImportedConeVerdict::passed, the import gate of `clean check`, `clean lake build`, export-cert and the module driver",
        unmodified: Outcome::refused(by::CLEAN_KERNEL, "ClosedRecheckRefusal::DeclarationRefused(planted): TypeMismatch"),
        mutant: Outcome::minted("ImportedConeVerdict::passed"),
    },
    Pin {
        site: "lean.leanchecker_fresh",
        mints: "exit 0 from the pinned `leanchecker --fresh P3Planted`, Lean's own kernel replaying the same bytes",
        unmodified: Outcome::refused(by::LEAN_KERNEL, "exit 1: (kernel) declaration type mismatch, 'planted'"),
        mutant: Outcome::refused(by::LEAN_KERNEL, "exit 1: (kernel) declaration type mismatch, 'planted'"),
    },
];

fn search_paths() -> Vec<PathBuf> {
    let mut search = vec![compiled_fixture_dir(FAMILY)];
    search.extend(default_search_paths());
    search
}

/// The module's closure as the re-check lanes load it: Lean's replay
/// environment, then the module and its imports through the `.olean` path.
fn load(module: &str) -> Environment {
    let mut env = Environment::for_lean_replay();
    let mut visited = hashbrown::HashSet::new();
    load_module_with_deps_shared_with_policy(
        &mut env,
        module,
        &search_paths(),
        &mut visited,
        OleanImportPolicy::default().refusing_refused_completions(),
    )
    .unwrap_or_else(|error| panic!("load {module}: {error}"));
    env.regenerate_missing_no_confusion();
    env
}

/// The module's one declaration, decoded from its `.olean` by the production converter.
fn own_constant(module: &str) -> ConstantInfo {
    let path = compiled_fixture_dir(FAMILY).join(format!("{module}.olean"));
    let parsed = parse_module_file(&path)
        .unwrap_or_else(|error| panic!("parse {}: {error}", path.display()));
    let mut own: Vec<ConstantInfo> = parsed
        .constants
        .iter()
        .map(|c| {
            convert_parsed_constant_to_const_info(c)
                .unwrap_or_else(|error| panic!("{module}: convert {}: {error}", c.name))
                .unwrap_or_else(|| panic!("{module}: {} is not a plain constant", c.name))
        })
        .collect();
    assert_eq!(own.len(), 1, "{module} must declare exactly one constant");
    own.remove(0)
}

fn targets(name: &str) -> BTreeSet<String> {
    BTreeSet::from([name.to_owned()])
}

type LaneOutcome = (usize, usize, BTreeMap<String, String>);

fn lane_observation(site: &'static str, outcome: &LaneOutcome) -> Observed {
    match outcome {
        (1, 0, errors) if errors.is_empty() => Observed::minted(site, LANE_MINT),
        (0, 1, errors) => {
            let message = errors
                .get(PLANTED)
                .unwrap_or_else(|| panic!("{site}: no error for `planted`: {errors:?}"));
            assert!(
                control::is_planted_mismatch(message),
                "{site}: `planted` refused for another reason: {message}"
            );
            Observed::refused(site, by::CLEAN_KERNEL, LANE_MISMATCH)
        }
        other => panic!("{site}: unexpected lane outcome {other:?}"),
    }
}

/// The three `verify_batch_full` lanes on the planted module, each after its
/// honest control.
fn probe_lanes() -> [Observed; 3] {
    let honest = load("P3Honest");
    let honest_targets = targets(HONEST);
    assert_eq!(
        typecheck_constants_full(&honest, &honest_targets, DEFAULT_HEARTBEAT_LIMIT),
        (1, 0, BTreeMap::new()),
        "eager lane: the honest theorem must verify"
    );
    assert_eq!(
        typecheck_constants_full_parallel(&honest, &honest_targets, 4, DEFAULT_HEARTBEAT_LIMIT),
        (1, 0, BTreeMap::new()),
        "parallel lane: the honest theorem must verify"
    );
    let mut honest = honest;
    let (pass, fail, errors, _) = typecheck_constants_full_streaming(
        &mut honest,
        &honest_targets,
        DEFAULT_HEARTBEAT_LIMIT,
        ProofValueElision::OpaqueAndTheorem,
        Some(1),
    );
    assert_eq!(
        (pass, fail, errors),
        (1, 0, BTreeMap::new()),
        "streaming lane: the honest theorem must verify"
    );

    let env = load("P3Planted");
    let planted = targets(PLANTED);
    let eager = typecheck_constants_full(&env, &planted, DEFAULT_HEARTBEAT_LIMIT);
    let parallel = typecheck_constants_full_parallel(&env, &planted, 4, DEFAULT_HEARTBEAT_LIMIT);
    let mut env = env;
    let (pass, fail, errors, _) = typecheck_constants_full_streaming(
        &mut env,
        &planted,
        DEFAULT_HEARTBEAT_LIMIT,
        ProofValueElision::OpaqueAndTheorem,
        Some(1),
    );
    [
        lane_observation("olean.typecheck_constants_full", &eager),
        lane_observation("olean.typecheck_constants_full_parallel", &parallel),
        lane_observation(
            "olean.typecheck_constants_full_streaming",
            &(pass, fail, errors),
        ),
    ]
}

/// `clean olean verify-batch --full-validation`: one environment, module after
/// module, `Init.Prelude` first, then the honest module, then the planted one.
fn probe_in_run() -> Observed {
    const SITE: &str = "olean.verify_one_module_in_run";
    let mut env = Environment::default();
    let search = search_paths();
    let mut known = HashSet::new();
    collect_new_env_names(&env, &mut known);
    let mut visited = hashbrown::HashSet::new();
    let mut not_admitted = BTreeSet::new();
    let mut run = |env: &mut Environment, module: &str, load_only: bool| {
        verify_one_module_with_mode_in_run(
            env,
            module,
            module,
            &search,
            &mut known,
            load_only,
            ValidationMode::Full,
            DEFAULT_HEARTBEAT_LIMIT,
            ProofValueElision::None,
            &mut visited,
            &mut not_admitted,
        )
    };
    assert!(
        run(&mut env, "Init.Prelude", true).load_ok,
        "{SITE}: Init.Prelude must load"
    );
    let honest = run(&mut env, "P3Honest", false);
    assert!(
        honest.load_ok && honest.tc_pass == 1 && honest.tc_fail == 0,
        "{SITE}: the honest module must verify: {honest:?}"
    );
    let result = run(&mut env, "P3Planted", false);
    assert!(
        result.load_ok,
        "{SITE}: the planted module must load: {result:?}"
    );
    match (result.tc_pass, result.tc_fail) {
        (1, 0) => Observed::minted(SITE, "tc_pass 1, tc_fail 0"),
        (0, 1) => {
            let message = result
                .tc_errors
                .get(PLANTED)
                .unwrap_or_else(|| panic!("{SITE}: {result:?}"));
            assert!(
                control::is_planted_mismatch(message),
                "{SITE}: refused for another reason: {message}"
            );
            Observed::refused(SITE, by::CLEAN_KERNEL, "tc_fail 1: TypeMismatch")
        }
        _ => panic!("{SITE}: unexpected module result {result:?}"),
    }
}

/// The header and the canonical `Nat` block of the minted fixture
/// `ndjson_minted/nat_add_literal.ndjson` (its first 51 lines: names 1-11,
/// levels 1-2, expressions 0-35; expression 6 is `Nat.zero`), then `False`.
fn export_prefix() -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/lean/v4.30.0-rc2/ndjson_minted/nat_add_literal.ndjson");
    let text = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("read {}: {error}", path.display()));
    let mut lines: Vec<&str> = text.lines().take(51).collect();
    assert!(
        lines[50].starts_with(r#"{"inductive""#),
        "line 51 must close the Nat block: {}",
        lines[50]
    );
    assert_eq!(
        lines[17], r#"{"const":{"name":2,"us":[]},"ie":6}"#,
        "expression 6 must be Nat.zero"
    );
    lines.extend([
        r#"{"in":12,"str":{"pre":0,"str":"False"}}"#,
        r#"{"in":13,"str":{"pre":12,"str":"rec"}}"#,
        r#"{"ie":36,"sort":0}"#,
        r#"{"const":{"name":12,"us":[]},"ie":37}"#,
        r#"{"ie":38,"sort":2}"#,
        r#"{"forallE":{"binderInfo":"default","body":38,"name":6,"type":37},"ie":39}"#,
        r#"{"bvar":1,"ie":40}"#,
        r#"{"bvar":0,"ie":41}"#,
        r#"{"app":{"arg":41,"fn":40},"ie":42}"#,
        r#"{"forallE":{"binderInfo":"default","body":42,"name":6,"type":37},"ie":43}"#,
        r#"{"forallE":{"binderInfo":"default","body":43,"name":5,"type":39},"ie":44}"#,
        r#"{"inductive":{"ctors":[],"recs":[{"all":[12],"isUnsafe":false,"k":false,"levelParams":[7],"name":13,"numIndices":0,"numMinors":0,"numMotives":1,"numParams":0,"rules":[],"type":44}],"types":[{"all":[12],"ctors":[],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":12,"numIndices":0,"numNested":0,"numParams":0,"type":36}]}}"#,
    ]);
    let mut out = lines.join("\n");
    out.push('\n');
    out
}

fn probe_ndjson() -> Observed {
    const SITE: &str = "olean.ndjson.check_export_reader";
    let prefix = export_prefix();
    let honest = check_export_reader(Cursor::new(prefix.clone()), ExportCheckOptions::default());
    assert_eq!(
        honest.exit,
        ExitClass::Accept,
        "{SITE}: the export without `planted` must be accepted: {honest:?}"
    );
    let planted = format!(
        "{prefix}{}\n{}\n",
        r#"{"in":14,"str":{"pre":0,"str":"planted"}}"#,
        r#"{"thm":{"all":[14],"levelParams":[],"name":14,"type":37,"value":6}}"#
    );
    let report = check_export_reader(Cursor::new(planted), ExportCheckOptions::default());
    let record = report
        .records
        .iter()
        .find(|record| record.name == PLANTED)
        .unwrap_or_else(|| panic!("{SITE}: no record for `planted`: {report:?}"));
    match (report.exit, record.verdict) {
        (ExitClass::Accept, DeclarationVerdict::Admitted) => {
            Observed::minted(SITE, "ExitClass::Accept, `planted` admitted")
        }
        (ExitClass::Reject, DeclarationVerdict::Refused) => {
            let first = report
                .first_refusal
                .as_ref()
                .unwrap_or_else(|| panic!("{SITE}: {report:?}"));
            assert_eq!(
                first.name, PLANTED,
                "{SITE}: the first refusal must be `planted`: {report:?}"
            );
            assert!(
                control::is_planted_mismatch(&first.reason),
                "{SITE}: refused for another reason: {}",
                first.reason
            );
            Observed::refused(
                SITE,
                by::CLEAN_KERNEL,
                "ExitClass::Reject, first refusal `planted`: TypeMismatch",
            )
        }
        other => panic!("{SITE}: unexpected outcome {other:?}: {report:?}"),
    }
}

/// The import gate: Clean's prelude as the base, and the decoded declaration
/// resident on top of it as an `.olean` import leaves it, unchecked.
fn probe_imported_cone_gate() -> Observed {
    const SITE: &str = "olean.imported_cone_gate";
    let base = Environment::with_prelude();
    let gate_over = |module: &str| {
        let constant = own_constant(module);
        let root = constant.name.clone();
        let mut env = base.clone();
        // SOUNDNESS: adversarial lane-input fixture only. Structural insertion
        // is not admission: it makes the decoded declaration resident the way
        // an `.olean` import does, so the gate whose re-check is under test
        // sees it; the environment never escapes this test.
        let rejected = env.extend_constants_structural(std::iter::once(constant));
        assert!(rejected.is_empty(), "{SITE}: {module}: {rejected:?}");
        ImportedConeGate::new(&base).check(&env, &BTreeSet::from([root]))
    };
    let honest = gate_over("P3Honest");
    assert!(
        honest.passed(false),
        "{SITE}: the honest theorem's cone must pass: {honest:?}"
    );
    let verdict = gate_over("P3Planted");
    if verdict.passed(false) {
        return Observed::minted(SITE, "ImportedConeVerdict::passed");
    }
    match verdict.refusals.as_slice() {
        [ClosedRecheckRefusal::DeclarationRefused { name, error }]
            if name == PLANTED && control::is_planted_mismatch(error) =>
        {
            Observed::refused(
                SITE,
                by::CLEAN_KERNEL,
                "ClosedRecheckRefusal::DeclarationRefused(planted): TypeMismatch",
            )
        }
        other => panic!("{SITE}: unexpected refusals {other:?}: {verdict:?}"),
    }
}

/// The pinned `leanchecker --fresh <module>` over the compiled family, with
/// the pinned `bin/` first on `PATH` so `lean --print-prefix` asks the pinned
/// binary (on this fleet a `lean` earlier on `PATH` may be another program).
fn leanchecker(module: &str) -> (Option<i32>, String) {
    let dir = compiled_fixture_dir(FAMILY);
    let lean = clean_olean::pinned_lean_binary().expect("the pinned Lean toolchain");
    let bin = lean.parent().expect("bin/").to_path_buf();
    let path = std::env::var_os("PATH").unwrap_or_default();
    let mut dirs = vec![bin.clone()];
    dirs.extend(std::env::split_paths(&path));
    let out = Command::new(bin.join("leanchecker"))
        .arg("--fresh")
        .arg(module)
        .current_dir(&dir)
        .env("LEAN_PATH", &dir)
        .env("PATH", std::env::join_paths(dirs).expect("PATH"))
        .output()
        .expect("run leanchecker");
    let mut said = String::from_utf8_lossy(&out.stdout).into_owned();
    said.push_str(&String::from_utf8_lossy(&out.stderr));
    (out.status.code(), said)
}

fn probe_leanchecker() -> Observed {
    const SITE: &str = "lean.leanchecker_fresh";
    let (code, err) = leanchecker("P3Honest");
    assert_eq!(
        code,
        Some(0),
        "{SITE}: leanchecker --fresh P3Honest must accept: {err}"
    );
    let (code, err) = leanchecker("P3Planted");
    match code {
        Some(0) => Observed::minted(SITE, "exit 0"),
        Some(1) if err.contains("(kernel) declaration type mismatch, 'planted'") => {
            Observed::refused(
                SITE,
                by::LEAN_KERNEL,
                "exit 1: (kernel) declaration type mismatch, 'planted'",
            )
        }
        other => panic!("{SITE}: unexpected leanchecker exit {other:?}: {err}"),
    }
}

#[test]
fn patched_kernel_control() {
    let mut observed = Vec::new();
    observed.extend(probe_lanes());
    observed.push(probe_in_run());
    observed.push(probe_ndjson());
    observed.push(probe_imported_cone_gate());
    observed.push(probe_leanchecker());
    // Every constant name the probes planted must be the one the pins speak of.
    assert_eq!(own_constant("P3Planted").name, Name::from_string(PLANTED));
    control::judge(PACKAGE, PINS, &observed);
}

#[test]
fn committed_record_matches_the_pins() {
    control::assert_record_matches_pins(PACKAGE, PINS);
}
