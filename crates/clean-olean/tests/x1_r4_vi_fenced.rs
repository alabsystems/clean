#![forbid(unsafe_code)]
// Copyright 2026 Andrew Yates | SPDX-License-Identifier: Apache-2.0
//! Plan unit X1 R4 item (vi) fenced `ReferenceKernel` qualification
//! (`docs/plans/SELF_PROOF_EXECUTION_PLAN_2026-11-12.md` §5 Lane X row X1;
//! `data/kcheck_execution_gaps.json` `c29_r4_vi_ground_acceptance_theorem`):
//!
//! Compiles the exact tracked R4 (vi) fixture
//! `tests/fixtures/advice_replay_checker/programs/c29_r4_vi_ground_acceptance_theorem.lean`
//! from source with the workspace-pinned `lean` binary, replays the compiled
//! `.olean` closure from an empty base through BOTH:
//!   1. Pinned Lean's independent kernel (`leanchecker --fresh C29R4ViGround`), and
//!   2. Clean's empty-base fenced `ReferenceKernel` (`reference_base_closed`),
//! pins every module-owned theorem statement, non-theorem definition/inductive
//! meaning (including transitive local-constant closure digests), and foundational
//! axiom closure (`⊆ {propext}`, zero `Classical.choice`, zero `Quot.sound`),
//! and verifies negative controls in both kernels:
//!   - Pinned Lean rejects `rejected/vi_false_acceptance_by_decide.lean` and
//!     `rejected/vi_false_acceptance_by_rfl.lean` for their pinned reasons;
//!   - Clean's fenced `ReferenceKernel` accepts re-entry of `Eq.refl true` at
//!     `accepts (conv 10 two (.lit 2) adv 0) = true` (forcing full kernel
//!     evaluation of the `whnf`/`conv` block under the fenced theory) and
//!     rejects `Eq.refl true` and the `decide` proof terms at the forged false
//!     statement `accepts (conv 10 two (.lit 3) adv 0) = true` and at `False`.
//!
//! Standing limits:
//! 1. Soundness claims on the self-proof route are per explicit universe bound.
//! 2. No generation proves more consistency than its base theory (`{propext}`).
//! 3. By design `kcheck` is to become Clean's proved checker once all six
//!    Plan §2.1 conditions hold in fact; this X1 R4 (vi) measurement flips no
//!    authority and retains the independent re-checker quorum.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};
use std::process::Command;

use clean_kernel::env::{Declaration, Environment};
use clean_kernel::{
    ConstantKind, Expr, KernelEnvError, KernelTypeError, Level, Name, ReferenceRefusal,
};
use clean_olean::{
    load_module_with_deps, pinned_lean_binary, read_artifact, reference_base_closed,
    require_pinned_lean_lib_path, ArtifactDepth, ClosedRecheckOptions,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

const MODULE_NAME: &str = "C29R4ViGround";
const TOOLCHAIN_FILE: &str = "../../lean-toolchain";
const FIXTURE_DIR: &str = "../../tests/fixtures/advice_replay_checker";
const PROGRAM_REL: &str = "programs/c29_r4_vi_ground_acceptance_theorem.lean";
const PINS_REL: &str = "c29_r4_vi_fenced_pins.json";
const PREIMAGES_REL: &str = "c29_r4_vi_fenced_preimages";

const REQUIRED_DEFS: &[&str] = &[
    "Tok",
    "Tm",
    "Refusal",
    "Refusal.show",
    "tokAt",
    "Tm.beq",
    "whnf",
    "conv",
    "infer",
    "accepts",
    "two",
    "adv",
    "main",
];

const HEADLINE_THEOREMS: &[&str] = &[
    "honest_accepted_by_rfl",
    "honest_accepted_by_decide",
    "corrupt_refused_by_decide",
];

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct PinRecord {
    schema_version: String,
    source_sha256: String,
    lean_version: String,
    statement_pins: BTreeMap<String, String>,
    meaning_pins: BTreeMap<String, String>,
    transitive_closure_pins: BTreeMap<String, String>,
    axiom_closures: BTreeMap<String, BTreeSet<String>>,
}

fn sha256_bytes(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|b| format!("{b:02x}"))
        .collect()
}

struct CanonicalPreimages {
    root: PathBuf,
    mint: bool,
}

impl CanonicalPreimages {
    fn digest<T: Serialize>(&self, section: &str, name: &Name, value: &T) -> String {
        let encoded = bincode::serde::encode_to_vec(value, bincode::config::standard())
            .expect("canonical bytes");
        let name = name.to_string();
        let mut chars = name.bytes();
        assert!(
            chars.next().is_some_and(|ch| ch.is_ascii_alphanumeric() || ch == b'_')
                && chars.all(|ch| ch.is_ascii_alphanumeric() || b"_.+-".contains(&ch)),
            "C29 declaration is not a file basename: {name}"
        );
        let directory = self.root.join(section);
        let path = directory.join(name);
        if self.mint {
            std::fs::create_dir_all(directory).expect("create canonical preimage directory");
            std::fs::write(&path, &encoded).expect("write canonical preimage");
        } else {
            let retained = std::fs::read(&path).unwrap_or_else(|error| {
                panic!("read canonical preimage {}: {error}", path.display())
            });
            assert!(
                retained == encoded,
                "canonical preimage drifted: {}",
                path.display()
            );
        }
        sha256_bytes(&encoded)
    }

    fn check_inventory(&self, section: &str, pins: &BTreeMap<String, String>) {
        let directory = self.root.join(section);
        let retained: BTreeSet<_> = std::fs::read_dir(directory)
            .expect("list canonical preimages")
            .map(|entry| {
                let entry = entry.expect("canonical preimage entry");
                assert!(entry.file_type().expect("canonical preimage kind").is_file());
                entry.file_name().into_string().expect("canonical preimage name")
            })
            .collect();
        assert_eq!(retained, pins.keys().cloned().collect(), "{section} preimage inventory");
    }
}

fn collect_expr_consts(expr: &Expr, out: &mut BTreeSet<Name>) {
    match expr.kind() {
        clean_kernel::ExprKind::Const(name, _) => {
            out.insert(name.clone());
        }
        clean_kernel::ExprKind::App(f, a) => {
            collect_expr_consts(f, out);
            collect_expr_consts(a, out);
        }
        clean_kernel::ExprKind::Lam(_, d, b) | clean_kernel::ExprKind::Pi(_, d, b) => {
            collect_expr_consts(d, out);
            collect_expr_consts(b, out);
        }
        clean_kernel::ExprKind::Let(_, ty, val, body, _) => {
            collect_expr_consts(ty, out);
            collect_expr_consts(val, out);
            collect_expr_consts(body, out);
        }
        clean_kernel::ExprKind::Proj(type_name, _, s) => {
            out.insert(type_name.clone());
            collect_expr_consts(s, out);
        }
        clean_kernel::ExprKind::MData(_, inner) => collect_expr_consts(inner, out),
        _ => {}
    }
}

fn transitive_local_digest(
    root: &Name,
    loaded: &Environment,
    local_targets: &BTreeSet<Name>,
    preimages: &CanonicalPreimages,
) -> String {
    let mut visited = BTreeSet::new();
    let mut stack = vec![root.clone()];
    while let Some(cur) = stack.pop() {
        if !local_targets.contains(&cur) || !visited.insert(cur.clone()) {
            continue;
        }
        let info = loaded.get_const(&cur).expect("local target in loaded env");
        let mut refs = BTreeSet::new();
        collect_expr_consts(&info.type_, &mut refs);
        if info.kind != ConstantKind::Theorem {
            if let Some(val) = &info.value {
                collect_expr_consts(val, &mut refs);
            }
        }
        if let Some(ind) = loaded.get_inductive(&cur) {
            for ctor in &ind.constructor_names {
                refs.insert(ctor.clone());
            }
        }
        for r in refs {
            if local_targets.contains(&r) && !visited.contains(&r) {
                stack.push(r);
            }
        }
    }

    let mut records = Vec::with_capacity(visited.len());
    for name in &visited {
        let info = loaded.get_const(name).expect("visited target");
        let params: Vec<String> = info.level_params.iter().map(ToString::to_string).collect();
        let value_for_hash = if info.kind == ConstantKind::Theorem {
            None
        } else {
            info.value.as_ref()
        };
        let ctor_list: Option<Vec<String>> = loaded.get_inductive(name).map(|ind| {
            ind.constructor_names
                .iter()
                .map(ToString::to_string)
                .collect()
        });
        records.push((
            name.to_string(),
            format!("{:?}", info.kind),
            params,
            &info.type_,
            value_for_hash,
            ctor_list,
        ));
    }
    preimages.digest("transitive_closure_pins", root, &records)
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

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join(FIXTURE_DIR)
}

#[test]
fn x1_r4_vi_ground_acceptance_rechecks_through_leanchecker_and_fenced_reference_kernel() {
    let toolchain_pin =
        std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(TOOLCHAIN_FILE))
            .expect("workspace lean-toolchain")
            .trim()
            .to_string();
    assert!(
        !toolchain_pin.is_empty(),
        "workspace lean-toolchain must be non-empty"
    );
    let fixture = fixture_dir();
    let preimages = CanonicalPreimages {
        root: fixture.join(PREIMAGES_REL),
        mint: std::env::var_os("MINT_X1_R4_VI_FENCED_PREIMAGES").is_some(),
    };
    let program_path = fixture.join(PROGRAM_REL);
    let source_bytes = std::fs::read(&program_path).expect("read c29 R4 (vi) fixture");
    let source_sha256 = sha256_bytes(&source_bytes);

    let lean = pinned_lean_binary().expect("pinned Lean binary");
    let lib = require_pinned_lean_lib_path().expect("pinned Lean lib path");
    let bin = lean.parent().expect("toolchain bin");

    let ver_out = Command::new(&lean)
        .arg("--version")
        .output()
        .expect("lean --version");
    assert!(ver_out.status.success(), "lean --version failed");
    let lean_version = String::from_utf8_lossy(&ver_out.stdout).trim().to_string();
    let expected_lean_version = std::fs::read_to_string(fixture.join("expected/LEAN_VERSION"))
        .expect("expected/LEAN_VERSION")
        .trim()
        .to_string();
    assert_eq!(
        lean_version, expected_lean_version,
        "pinned Lean binary must match X1 fixture's LEAN_VERSION"
    );

    // Negative controls in Kernel 1 (pinned Lean): both false-acceptance twins must fail.
    for (rejected_rel, expected_err) in [
        (
            "rejected/vi_false_acceptance_by_decide.lean",
            "Tactic `decide` proved that the proposition",
        ),
        (
            "rejected/vi_false_acceptance_by_rfl.lean",
            "Not a definitional equality",
        ),
    ] {
        let rej_path = fixture.join(rejected_rel);
        let out = Command::new(&lean)
            .arg(&rej_path)
            .output()
            .expect("run pinned Lean on rejected R4 (vi) control");
        assert!(
            !out.status.success(),
            "pinned Lean unexpectedly accepted {rejected_rel}"
        );
        let combined = format!(
            "{}\n{}",
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        );
        assert!(
            combined.contains(expected_err),
            "{rejected_rel}: expected `{expected_err}`, got:\n{combined}"
        );
    }

    // Fresh compilation of exact `c29_r4_vi_ground_acceptance_theorem.lean` bytes.
    let workdir = tempfile::tempdir().expect("scratch compile dir");
    let staged_lean = workdir.path().join(format!("{MODULE_NAME}.lean"));
    let staged_olean = workdir.path().join(format!("{MODULE_NAME}.olean"));
    std::fs::write(&staged_lean, &source_bytes).expect("stage C29R4ViGround.lean");

    let compile_out = Command::new(&lean)
        .current_dir(workdir.path())
        .args([
            "--root",
            ".",
            "-o",
            &format!("{MODULE_NAME}.olean"),
            &format!("{MODULE_NAME}.lean"),
        ])
        .output()
        .expect("compile C29R4ViGround.lean");
    assert!(
        compile_out.status.success() && staged_olean.is_file(),
        "compiling {PROGRAM_REL} failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&compile_out.stdout),
        String::from_utf8_lossy(&compile_out.stderr)
    );

    // Kernel 1: `leanchecker --fresh C29R4ViGround`.
    let mut paths = vec![bin.to_path_buf()];
    paths.extend(std::env::split_paths(
        &std::env::var_os("PATH").unwrap_or_default(),
    ));
    let replay = Command::new(bin.join("leanchecker"))
        .args(["--fresh", MODULE_NAME])
        .current_dir(workdir.path())
        .env(
            "LEAN_PATH",
            std::env::join_paths([workdir.path(), lib.as_path()]).expect("LEAN_PATH"),
        )
        .env("PATH", std::env::join_paths(paths).expect("PATH"))
        .output()
        .expect("leanchecker --fresh C29R4ViGround");
    assert!(
        replay.status.success(),
        "leanchecker --fresh {MODULE_NAME} failed:\n{}\n{}",
        String::from_utf8_lossy(&replay.stdout),
        String::from_utf8_lossy(&replay.stderr)
    );

    // Load `.olean` closure and select all module-owned declarations.
    let mut loaded = Environment::for_lean_replay();
    let summaries = load_module_with_deps(
        &mut loaded,
        MODULE_NAME,
        &[workdir.path().to_path_buf(), lib],
    )
    .expect("load C29R4ViGround with Init deps");
    let not_replayable: BTreeSet<&str> = summaries
        .iter()
        .flat_map(|s| s.skipped_not_replayable.iter().map(String::as_str))
        .collect();

    let artifact = read_artifact(MODULE_NAME, &staged_olean, ArtifactDepth::Names)
        .expect("read C29R4ViGround.olean names");
    let mut targets = BTreeSet::new();
    let mut compiler_copies = BTreeSet::new();
    for name in artifact.names {
        let text = name.to_string();
        if loaded.get_const(&name).is_none() {
            assert!(
                text.ends_with("._unsafe_rec") && not_replayable.contains(text.as_str()),
                "{MODULE_NAME} declares {name}, absent without ._unsafe_rec mark"
            );
            assert!(compiler_copies.insert(text), "duplicate {name}");
            continue;
        }
        assert!(
            !loaded.is_unsafe(&name) && !loaded.is_partial(&name),
            "{MODULE_NAME} declares {name} unsafe or partial"
        );
        targets.insert(name);
    }
    for copy in &compiler_copies {
        let base_def = copy.strip_suffix("._unsafe_rec").expect("checked suffix");
        assert!(
            targets.contains(&Name::from_string(base_def)),
            "{copy} has no safe companion in targets"
        );
    }

    for req in REQUIRED_DEFS {
        assert!(
            targets.contains(&Name::from_string(req)),
            "missing required R4 (vi) declaration `{req}`"
        );
    }
    for thm in HEADLINE_THEOREMS {
        let name = Name::from_string(thm);
        let info = loaded.get_const(&name).expect("headline theorem present");
        assert!(
            targets.contains(&name) && info.kind == ConstantKind::Theorem && info.value.is_some(),
            "`{thm}` must be a value-bearing Theorem in {MODULE_NAME}"
        );
    }

    // Kernel 2: Clean's empty-base fenced ReferenceKernel (`reference_base_closed`).
    let base = reference_base_closed(&loaded, &targets, &ClosedRecheckOptions::default())
        .expect("fenced ReferenceKernel replay construction");
    assert!(
        base.report.passed() && base.entry_refusals.is_empty(),
        "fenced ReferenceKernel refused {MODULE_NAME}:\n{}\n{:?}",
        base.report.verdict_sentence(),
        base.entry_refusals
    );
    let mut kernel = base.into_kernel().expect("fenced ReferenceKernel instance");

    let mut statement_pins = BTreeMap::new();
    let mut meaning_pins = BTreeMap::new();
    let mut transitive_closure_pins = BTreeMap::new();
    let mut axiom_closures = BTreeMap::new();

    for name in &targets {
        let c = loaded.get_const(name).expect("target in loaded");
        let params: Vec<String> = c.level_params.iter().map(ToString::to_string).collect();
        let admitted = kernel.environment();
        let mut closure = admitted.axiom_deps(name).expect("admitted axiom_deps");
        closure.extend(
            admitted
                .foundational_axiom_deps(name)
                .expect("admitted foundational_axiom_deps"),
        );
        assert!(
            closure.iter().all(clean_kernel::env::is_foundational_axiom),
            "{name} depends on non-foundational axiom: {closure:?}"
        );
        assert!(
            !closure.contains(&Name::from_string("Classical.choice")),
            "{name} unexpectedly depends on Classical.choice: {closure:?}"
        );
        assert!(
            !closure.contains(&Name::from_string("Quot.sound")),
            "{name} unexpectedly depends on Quot.sound: {closure:?}"
        );
        transitive_closure_pins.insert(
            name.to_string(),
            transitive_local_digest(name, &loaded, &targets, &preimages),
        );
        if c.kind == ConstantKind::Theorem {
            statement_pins.insert(
                name.to_string(),
                preimages.digest("statement_pins", name, &(&params, &c.type_)),
            );
            axiom_closures.insert(
                name.to_string(),
                closure.iter().map(ToString::to_string).collect(),
            );
        } else {
            meaning_pins.insert(
                name.to_string(),
                preimages.digest(
                    "meaning_pins",
                    name,
                    &(format!("{:?}", c.kind), &params, &c.type_, &c.value),
                ),
            );
        }
    }

    // Build the exact forged false-acceptance statement:
    //   `Eq.{1} Bool (accepts (conv 10 two (Tm.lit 3) adv 0)) Bool.true`
    // by taking `corrupt_refused_by_decide`'s LHS (`accepts (conv 10 two (.lit 3) adv 0)`)
    // and equating it to `Bool.true` instead of `Bool.false`!
    let corrupt_thm = loaded
        .get_const(&Name::from_string("corrupt_refused_by_decide"))
        .expect("corrupt_refused_by_decide");
    let corrupt_args = corrupt_thm.type_.get_app_args();
    assert_eq!(
        corrupt_args.len(),
        3,
        "corrupt_refused_by_decide must be an Eq application"
    );
    let bool_ty = (*corrupt_args[0]).clone();
    let corrupt_lhs = (*corrupt_args[1]).clone();
    let honest_thm = loaded
        .get_const(&Name::from_string("honest_accepted_by_rfl"))
        .expect("honest_accepted_by_rfl");
    let honest_args = honest_thm.type_.get_app_args();
    assert_eq!(honest_args.len(), 3);
    let bool_true = (*honest_args[2]).clone();
    assert_ne!(
        corrupt_lhs, *honest_args[1],
        "corrupt LHS (.lit 3) must differ from honest LHS (.lit 2)"
    );
    let forged_corrupt_accepted_stmt = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
                bool_ty,
            ),
            corrupt_lhs,
        ),
        bool_true,
    );

    // Every headline proof re-admits at its own statement, and is refused by TypeMismatch
    // at BOTH `forged_corrupt_accepted_stmt` AND `False` inside the fenced ReferenceKernel!
    for (idx, thm_name) in HEADLINE_THEOREMS.iter().enumerate() {
        let info = loaded
            .get_const(&Name::from_string(thm_name))
            .expect("headline theorem");
        let proof = info.value.clone().expect("proof value");

        kernel
            .add_checked(Declaration::Theorem {
                name: Name::from_string(&format!("C29R4ViGround.Controls.honest_reentry_{idx}")),
                level_params: info.level_params.clone(),
                type_: info.type_.clone(),
                value: proof.clone(),
            })
            .unwrap_or_else(|e| panic!("honest re-entry failed for {thm_name}: {e:?}"));

        let forged_res = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("C29R4ViGround.Controls.forged_corrupt_{idx}")),
            level_params: info.level_params.clone(),
            type_: forged_corrupt_accepted_stmt.clone(),
            value: proof.clone(),
        });
        assert!(
            is_type_mismatch(&forged_res),
            "fenced ReferenceKernel failed to reject {thm_name}'s proof at forged corrupt acceptance: {forged_res:?}"
        );

        let false_res = kernel.add_checked(Declaration::Theorem {
            name: Name::from_string(&format!("C29R4ViGround.Controls.false_{idx}")),
            level_params: info.level_params.clone(),
            type_: Expr::const_str("False"),
            value: proof,
        });
        assert!(
            is_type_mismatch(&false_res),
            "fenced ReferenceKernel failed to reject {thm_name}'s proof at False: {false_res:?}"
        );
    }

    preimages.check_inventory("statement_pins", &statement_pins);
    preimages.check_inventory("meaning_pins", &meaning_pins);
    preimages.check_inventory("transitive_closure_pins", &transitive_closure_pins);

    let live_pins = PinRecord {
        schema_version: "clean-x1-r4-vi-fenced-pins-v1".to_string(),
        source_sha256,
        lean_version,
        statement_pins,
        meaning_pins,
        transitive_closure_pins,
        axiom_closures,
    };

    let pins_path = fixture.join(PINS_REL);
    if std::env::var_os("MINT_X1_R4_VI_FENCED_PINS").is_some() {
        std::fs::write(
            &pins_path,
            format!(
                "{}\n",
                serde_json::to_string_pretty(&live_pins).expect("serialize PinRecord")
            ),
        )
        .expect("write c29_r4_vi_fenced_pins.json");
    }

    let committed: PinRecord =
        serde_json::from_str(&std::fs::read_to_string(&pins_path).unwrap_or_else(|e| {
            panic!(
                "missing {}: {e} (mint with MINT_X1_R4_VI_FENCED_PINS=1)",
                pins_path.display()
            )
        }))
        .expect("parse c29_r4_vi_fenced_pins.json");
    assert_eq!(
        live_pins,
        committed,
        "R4 (vi) fenced ReferenceKernel pins drifted from {}",
        pins_path.display()
    );
}
