// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Ph3 I.2 / Clean F5 qualification: one pinned-`Init` environment constructor
//! shared by `clean check` (`EnvironmentSetup::PINNED_INIT` / `PreludeFlavor::PinnedInit`)
//! and the island (`EnvironmentSetup::ISLAND_PINNED_INIT`, `island_environment_in_world`,
//! `island_environment_for_header`), plus the island prelude's fail-closed refusal of
//! value-less constants, axioms, unsafe/partial declarations, and bootstrap stubs.

use std::collections::{BTreeSet, HashSet};
use std::path::{Path, PathBuf};
use std::sync::{Arc, OnceLock};

use clean_elab::module_driver::source_graph::{
    CapturedSourceGraph, CapturedSourceModule, SourceImport,
};
use clean_elab::module_driver::{
    elaborate_prelude_header, foundation_import_base, module_environment_for_header_in_world,
    module_file_context_in_world, parse_module_in_world, EnvironmentSetup, PreludeFlavor,
    VerdictKind,
};
use clean_elab::{
    elaborate_decl_and_register_with_context, is_island_environment, island_environment_for_header,
    island_environment_in_world, pinned_init_environment_setup, preprocess_decl_with_context,
    ElabResult,
};
use clean_kernel::env::{Declaration, Environment};
use clean_kernel::lean_world::LeanWorld;
use clean_kernel::{Expr, Name};
use clean_parser::{FileHeader, Parser};

fn repo_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("crates/")
        .parent()
        .expect("repo root")
        .to_path_buf()
}

fn run_on_large_stack<F: FnOnce() + Send + 'static>(name: &str, f: F) {
    std::thread::Builder::new()
        .name(name.to_string())
        .stack_size(128 << 20)
        .spawn(f)
        .expect("spawn test thread")
        .join()
        .expect("join test thread");
}

struct SharedInitFixture {
    check_env: Environment,
    island_env: Environment,
}

fn shared_init_fixture() -> &'static SharedInitFixture {
    static FIXTURE: OnceLock<SharedInitFixture> = OnceLock::new();
    FIXTURE.get_or_init(|| {
        let decision = clean_olean::source_world_for_snapshot().expect("pinned snapshot world");
        let default_header = FileHeader::default();
        let (check_env, _) = module_environment_for_header_in_world(
            EnvironmentSetup::PINNED_INIT,
            &decision,
            &default_header,
        )
        .expect("module driver pinned Init");
        let (island_env, _) =
            island_environment_in_world(&decision, &default_header).expect("island in world");
        SharedInitFixture {
            check_env,
            island_env,
        }
    })
}

fn elaborate_unit(
    env: &mut Environment,
    decision: &clean_olean::SourceWorldDecision,
    module_name: &str,
    virtual_path: &Path,
    source: &str,
    already_mounted: &HashSet<String>,
) -> Result<BTreeSet<Name>, String> {
    let header = Parser::parse_header(source).map_err(|e| e.to_string())?;
    let report = parse_module_in_world(virtual_path, source, decision)
        .1
        .map_err(|e| e.to_string())?;
    assert!(
        report.diagnostics.is_empty(),
        "{module_name}: parser diagnostics must be empty: {:?}",
        report.diagnostics
    );
    let mut context = module_file_context_in_world(virtual_path, decision);
    context.set_main_module(Name::from_string(module_name));
    let body = elaborate_prelude_header(env, &report.decls, &mut context)
        .map_err(|e| format!("{module_name} prelude header: {e}"))?;

    let imports = decision.imports().map_err(|e| e.to_string())?;
    let search_paths = clean_olean::search_paths_in_world(imports);
    for imp in &header.imports {
        let dotted = imp.module.name().to_string();
        if already_mounted.contains(&dotted) {
            continue;
        }
        clean_olean::load_module_with_deps(env, &dotted, &search_paths)
            .map_err(|e| format!("{module_name} import `{dotted}`: {e}"))?;
    }

    let mut cited = BTreeSet::new();
    for decl in body {
        let processed = preprocess_decl_with_context(decl, &mut context);
        let result = elaborate_decl_and_register_with_context(env, &processed, &mut context)
            .map_err(|e| format!("{module_name}: {e}"))?;
        if let Some(err) = result.source_error_message() {
            return Err(format!("{module_name}: {err}"));
        }
        collect_cited_roots_deep(env, &result, &mut cited);
    }
    Ok(cited)
}

fn collect_cited_roots_deep(env: &Environment, result: &ElabResult, out: &mut BTreeSet<Name>) {
    match result {
        ElabResult::Diagnosed { result, .. } => collect_cited_roots_deep(env, result, out),
        ElabResult::Multiple(items) => {
            for item in items {
                collect_cited_roots_deep(env, item, out);
            }
        }
        other => out.extend(other.cited_roots(env)),
    }
}

#[test]
fn pinned_init_constructor_shared_between_module_driver_and_island() {
    run_on_large_stack("f5-shared-pinned-init", || {
        let setup = pinned_init_environment_setup();
        assert_eq!(setup, EnvironmentSetup::PINNED_INIT);
        assert_eq!(setup.prelude, PreludeFlavor::PinnedInit);
        assert_eq!(
            EnvironmentSetup::ISLAND_PINNED_INIT.prelude,
            PreludeFlavor::IslandPinnedInit
        );

        let mut prelude_header = FileHeader::default();
        prelude_header.is_prelude = true;
        let (bare_island_env, _) =
            island_environment_for_header(&prelude_header).expect("bare snapshot island");
        assert!(is_island_environment(&bare_island_env));
        assert_eq!(bare_island_env.num_constants(), 0);

        let fixture = shared_init_fixture();
        let check_env = &fixture.check_env;
        let island_env = &fixture.island_env;

        assert!(!is_island_environment(check_env));
        assert!(is_island_environment(island_env));
        assert_eq!(check_env.num_constants(), island_env.num_constants());

        for env in [check_env, island_env] {
            assert_eq!(
                clean_olean::environment_world(env),
                Some(LeanWorld::ORACLE.tag())
            );
            let decidable = env
                .get_inductive(&Name::from_string("Decidable"))
                .expect("genuine Decidable");
            assert_eq!(
                decidable.constructor_names,
                vec![
                    Name::from_string("Decidable.isFalse"),
                    Name::from_string("Decidable.isTrue"),
                ],
                "must carry pinned v4.30.0-rc2 Decidable"
            );
            assert!(
                env.get_const(&Name::from_string("UInt16.not_neg_one"))
                    .is_some(),
                "must load full pinned Init, not Init.Prelude or handwritten builtin"
            );
            assert!(
                env.get_const(&Name::from_string("trustedArith")).is_none()
                    && env.get_const(&Name::from_string("trustedAy")).is_none(),
                "pinned Init over Environment::for_lean_replay must seed zero Clean synthetic trust markers"
            );
        }

        for info in check_env.constants() {
            let other = island_env
                .get_const(&info.name)
                .unwrap_or_else(|| panic!("missing `{}` in island env", info.name));
            assert_eq!(info.kind, other.kind, "kind mismatch on {}", info.name);
            assert_eq!(info.type_, other.type_, "type mismatch on {}", info.name);
            assert_eq!(info.value, other.value, "value mismatch on {}", info.name);
        }

        let decision = clean_olean::source_world_for_snapshot().expect("pinned snapshot world");
        let mut gate = foundation_import_base(&decision).expect("Ax0 foundation gate");
        let probe_roots = BTreeSet::from([Name::from_string("Nat.add_comm")]);
        let v_check = gate.check(check_env, &probe_roots);
        assert!(v_check.passed(false), "{}", v_check.refusal_summary(false));
        let v_island = gate.check(island_env, &probe_roots);
        assert!(
            v_island.passed(false),
            "{}",
            v_island.refusal_summary(false)
        );
    });
}

#[test]
fn island_elaborates_real_cicl_level_and_level_cases_with_ax0_cone() {
    run_on_large_stack("f5-cicl-level-island", || {
        let root = repo_root();
        let level_path = root.join("theories/cic_l/CICL/Level.lean");
        let cases_path = root.join("theories/cic_l/CICL/LevelCases.lean");
        let level_src: Arc<str> = std::fs::read_to_string(&level_path)
            .expect("read CICL/Level.lean")
            .into();
        let cases_src: Arc<str> = std::fs::read_to_string(&cases_path)
            .expect("read CICL/LevelCases.lean")
            .into();

        let decision = clean_olean::source_world_for_snapshot().expect("pinned snapshot world");
        let level_mod = Name::from_string("CICL.Level");
        let cases_mod = Name::from_string("CICL.LevelCases");
        let graph = CapturedSourceGraph::new(vec![
            CapturedSourceModule {
                name: level_mod.clone(),
                path: PathBuf::from("CICL/Level.lean"),
                source: level_src,
            },
            CapturedSourceModule {
                name: cases_mod.clone(),
                path: PathBuf::from("CICL/LevelCases.lean"),
                source: cases_src,
            },
        ])
        .expect("captured CICL.Level + CICL.LevelCases graph");

        let output = graph
            .elaborate(
                std::slice::from_ref(&cases_mod),
                EnvironmentSetup::ISLAND_PINNED_INIT,
                &decision,
                &mut |_from: &CapturedSourceModule, imported: &Name| {
                    if *imported == level_mod {
                        Ok(SourceImport::Captured(level_mod.clone()))
                    } else {
                        Ok(SourceImport::Artifact)
                    }
                },
            )
            .expect("elaborate CICL.Level + CICL.LevelCases in island");

        assert!(is_island_environment(&output.environment));
        for mod_name in [&level_mod, &cases_mod] {
            let mod_out = &output.modules[mod_name];
            assert!(
                !mod_out.report.verdicts.is_empty()
                    && mod_out
                        .report
                        .verdicts
                        .iter()
                        .all(|v| v.kind == VerdictKind::Passed)
                    && mod_out.declarations.iter().all(|d| !d.refused),
                "{mod_name} island elaboration report had non-passing verdicts: {:?}",
                mod_out.report
            );
        }
        assert!(output
            .environment
            .get_const(&Name::from_string("CICL.Level.eval"))
            .is_some());

        let all_roots: BTreeSet<Name> = output
            .modules
            .values()
            .flat_map(|m| m.introduced.iter().cloned())
            .collect();
        let mut import_gate = foundation_import_base(&decision).expect("Ax0 foundation gate");
        let verdict = import_gate.check(&output.environment, &all_roots);
        assert!(
            verdict.passed(false),
            "island cone must re-admit over canonical Ax0 foundations: {}",
            verdict.refusal_summary(false)
        );
    });
}

#[test]
fn island_fence_refuses_valueless_axioms_stubs_and_bad_imports() {
    run_on_large_stack("f5-island-negative-controls", || {
        let decision = clean_olean::source_world_for_snapshot().expect("pinned snapshot world");
        let base_env = &shared_init_fixture().island_env;
        let mounted = HashSet::new();
        let vpath = Path::new("IslandProbe.lean");

        // Positive control: body-bearing `opaque` and ordinary `def` succeed.
        {
            let mut env = base_env.clone();
            elaborate_unit(
                &mut env,
                &decision,
                "IslandPositive",
                vpath,
                "opaque islandConst : Nat := 7\ndef islandUse : Nat := islandConst + 1\n",
                &mounted,
            )
            .expect("body-bearing opaque and pure def must pass");
            assert!(env
                .get_const(&Name::from_string("islandConst"))
                .expect("islandConst")
                .value
                .is_some());
        }

        // Bootstrap-stub suppression control: in a bare prelude island (without Init.System.IO),
        // referencing `IO.println` must fail rather than synthesizing Clean's bootstrap IO stubs.
        {
            let mut bare_header = FileHeader::default();
            bare_header.is_prelude = true;
            let (mut bare_env, _) =
                island_environment_in_world(&decision, &bare_header).expect("bare island env");
            let io_err = elaborate_unit(
                &mut bare_env,
                &decision,
                "BareIoBootstrapStub",
                vpath,
                "prelude\ndef badIo := IO.println\n",
                &mounted,
            )
            .expect_err("bare island must suppress bootstrap IO stubs");
            assert!(
                io_err.contains("IO"),
                "expected unknown IO error in bare island, got `{io_err}`"
            );
        }

        // Negative controls over full pinned Init: direct axiom, body-less opaque,
        // unsafe, partial, sorry, duplicate Nat.
        for (label, bad_src, needle) in [
            ("direct_axiom", "axiom planted : False\n", "axiom"),
            ("bodyless_opaque", "opaque uninhabitedBody : False\n", ""),
            ("unsafe_def", "unsafe def badUnsafe : Nat := 0\n", "unsafe"),
            (
                "partial_def",
                "partial def badLoop (n : Nat) : Nat := badLoop n\n",
                "",
            ),
            ("sorry_proof", "theorem badSorry : False := sorry\n", ""),
            ("duplicate_nat", "inductive Nat where\n  | zero : Nat\n", ""),
        ] {
            let mut env = base_env.clone();
            let err = elaborate_unit(&mut env, &decision, label, vpath, bad_src, &mounted)
                .expect_err(label);
            if !needle.is_empty() {
                assert!(
                    err.contains(needle),
                    "{label}: expected `{needle}` in `{err}`"
                );
            }
        }

        // Direct and transitive citation of a non-foundational value-less constant.
        let mut tainted_env = base_env.clone();
        let stub_name = Name::from_string("extValuelessStub");
        tainted_env
            .add_decl_structural(Declaration::Axiom {
                name: stub_name.clone(),
                level_params: Vec::new(),
                type_: Expr::const_(Name::from_string("Nat"), Vec::new()),
            })
            .expect("inject structural value-less stub");

        let direct_err = elaborate_unit(
            &mut tainted_env,
            &decision,
            "DirectStub",
            vpath,
            "def directUse : Nat := extValuelessStub\n",
            &mounted,
        )
        .expect_err("direct citation of value-less stub must fail");
        assert!(
            direct_err.contains("extValuelessStub"),
            "direct error must name the value-less stub: {direct_err}"
        );
        assert!(tainted_env
            .get_const(&Name::from_string("directUse"))
            .is_none());

        tainted_env
            .add_decl_structural(Declaration::Definition {
                name: Name::from_string("midWrapper"),
                level_params: Vec::new(),
                type_: Expr::const_(Name::from_string("Nat"), Vec::new()),
                value: Expr::const_(stub_name, Vec::new()),
                is_reducible: true,
            })
            .expect("inject structural wrapper with value");

        let trans_err = elaborate_unit(
            &mut tainted_env,
            &decision,
            "TransitiveStub",
            vpath,
            "def transitiveUse : Nat := midWrapper\n",
            &mounted,
        )
        .expect_err("transitive citation of value-less stub must fail");
        assert!(
            trans_err.contains("extValuelessStub"),
            "transitive error must name the underlying value-less stub: {trans_err}"
        );
        assert!(tainted_env
            .get_const(&Name::from_string("transitiveUse"))
            .is_none());

        // Fictional Init import refuses fail-closed.
        let mut import_env = base_env.clone();
        let import_err = elaborate_unit(
            &mut import_env,
            &decision,
            "BadImport",
            vpath,
            "import Init.DoesNotExist\ndef unreachableDef : Nat := 0\n",
            &mounted,
        )
        .expect_err("fictional Init import must fail");
        assert!(
            import_err.contains("Init.DoesNotExist"),
            "import error must name missing module: {import_err}"
        );
    });
}
