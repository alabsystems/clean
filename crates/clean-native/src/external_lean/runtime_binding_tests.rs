// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_compiler::pass_manager::{compile_lcnf_decls_in_runtime_closure, PipelineConfig};

const LATE: &str = "\ndef lateFast (x : Leaf) : Leaf := x\ndef lateSlow (_ : Leaf) : Leaf := targetVal\ndef beforeLate (x : Leaf) : Leaf := lateSlow x\nattribute [implemented_by lateFast] lateSlow\n";

#[test]
fn actual_irrelevant_late_import_context_has_explicit_scoped_route_and_legacy_refusal() {
    let program = program(&format!("{SOURCE}{LATE}"));
    let legacy = match program.select(&n("handoff"), 0) {
        Err(e) => e,
        Ok(_) => panic!("legacy order refusal lost"),
    };
    assert!(
        legacy.to_string().contains("native-implemented-by-order"),
        "{legacy}"
    );
    let selected = program.select_in_runtime_closure(&n("handoff"), 0).unwrap();
    assert!(selected.runtime_binding_closure.is_some());
    let c = selected.emit(EmitFormat::C).unwrap();
    let dir = tempfile::tempdir().unwrap();
    let binary=crate::native_build::build_extract_executable(dir.path(),"",&c,"int main(void) { for(unsigned tag=0;tag<2;++tag) { clean_obj* out=l_handoff(clean_box(tag)); if(clean_obj_tag(out)!=tag) return 1; } return 0; }").unwrap();
    assert!(Command::new(binary).status().unwrap().success());
    assert!(
        program.select(&n("handoff"), 0).is_err(),
        "scoped success must not clear order records"
    );
}

#[test]
fn actual_selected_and_runtime_implementation_transitive_late_calls_refuse() {
    let source=format!("{SOURCE}{LATE}\ndef selectedLate : Leaf := lateSlow targetVal\ndef transitiveImplementation (x : Leaf) : Leaf := lateSlow x\n@[implemented_by transitiveImplementation] def transitiveLogical (x : Leaf) : Leaf := x\ndef selectedRuntime : Leaf := transitiveLogical targetVal\n");
    let program = program(&source);
    for root in ["selectedLate", "selectedRuntime"] {
        assert!(program
            .inspect_owned_declaration(&n(root))
            .unwrap()
            .replay_verdict()
            .passed(false));
        let error = match program.select_in_runtime_closure(&n(root), 0) {
            Err(e) => e,
            Ok(_) => panic!("late runtime dependency admitted: {root}"),
        };
        assert!(
            error.to_string().contains("implemented-by-order"),
            "{root}: {error}"
        );
        assert!(error.to_string().contains("lateSlow"), "{root}: {error}");
    }
}

#[test]
fn actual_source_and_import_changes_cannot_reuse_an_old_runtime_contract() {
    let dir = tempfile::tempdir().unwrap();
    let source = dir.path().join("Handoff.lean");
    let original = program_at(&source, &format!("{SOURCE}{LATE}"));
    let old = original
        .select_in_runtime_closure(&n("handoff"), 0)
        .unwrap();
    let altered = SOURCE.replace("(recordLeaf x)", "(recordLeaf Flag.off)");
    let changed = program_at(&source, &format!("{altered}{LATE}"));
    let changed_selection = changed.select_in_runtime_closure(&n("handoff"), 0).unwrap();
    assert_ne!(
        old.source_capture().snapshot_blake3,
        changed_selection.source_capture().snapshot_blake3
    );
    let contract = old.runtime_binding_closure.as_ref().unwrap();
    assert!(compile_lcnf_decls_in_runtime_closure(
        &changed_selection.decls,
        &changed_selection.env,
        &PipelineConfig::default(),
        contract
    )
    .is_err());

    // Compile a real alternate imported Target with the official measured430
    // frontend. The main source bytes are restored unchanged; only the actual
    // imported targetVal kernel body changes (Leaf.same Leaf.mk -> Leaf.mk).
    let imports = dir.path().join("imports");
    std::fs::create_dir(&imports).unwrap();
    std::fs::copy(fixture().join("Init.olean"), imports.join("Init.olean")).unwrap();
    let target = imports.join("Target.lean");
    std::fs::write(
        &target,
        "prelude\nimport Init\ndef targetVal : Leaf := Leaf.mk\n",
    )
    .unwrap();
    let world = clean_olean::source_world_for_file(&target, Some(LeanWorld::ORACLE)).unwrap();
    let Ok(ImportWorld::Explicit { lib, .. }) = world.imports() else {
        panic!("explicit world")
    };
    let lean = lib.parent().unwrap().parent().unwrap().join("bin/lean");
    let output = Command::new(lean)
        .current_dir(&imports)
        .env_clear()
        .env("LEAN_PATH", &imports)
        .arg("--root")
        .arg(&imports)
        .arg("-o")
        .arg(imports.join("Target.olean"))
        .arg(&target)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    std::fs::write(&source, format!("{SOURCE}{LATE}")).unwrap();
    let changed_import = ExternalLeanProgram::elaborate(ExternalLeanInput {
        file: &source,
        module: &n("Handoff"),
        imports: &[n("Target")],
        search_paths: &[imports],
        world: LeanWorld::ORACLE,
    })
    .unwrap();
    let imported = changed_import
        .select_in_runtime_closure(&n("handoff"), 0)
        .unwrap();
    assert_eq!(
        old.source_capture().sources[0].source,
        imported.source_capture().sources[0].source
    );
    assert_ne!(old.closure_digest(), imported.closure_digest());
    assert!(compile_lcnf_decls_in_runtime_closure(
        &imported.decls,
        &imported.env,
        &PipelineConfig::default(),
        contract
    )
    .is_err());
}

#[test]
fn scoped_selection_keeps_kernel_replay_and_structural_name_membership() {
    let source=format!("{SOURCE}{LATE}\nnamespace Shadow\ndef key (x : Flag) : Flag := x\nend Shadow\ndef «Shadow.key» (_ : Flag) : Flag := Flag.off\ndef shadowRoot (x : Flag) : Flag := Shadow.key x\n");
    let mut program = program(&source);
    let selected = program
        .select_in_runtime_closure(&n("shadowRoot"), 0)
        .unwrap();
    let quoted = Name::anon().str("Shadow.key");
    assert_ne!(quoted, n("Shadow.key"));
    let contract = selected.runtime_binding_closure.as_ref().unwrap();
    assert!(clean_compiler::constant_to_decl_in_runtime_closure(
        &program.env,
        program.env.get_const(&quoted).unwrap(),
        contract
    )
    .is_err());
    replace(&mut program, "Pair.mk", |info| {
        info.type_ = Expr::const_(n("Leaf"), vec![])
    });
    assert!(matches!(
        program.select_in_runtime_closure(&n("handoff"), 0),
        Err(ExternalLeanError::Replay { .. })
    ));
}

#[test]
fn scoped_route_preserves_eligibility_extern_and_implemented_by_root_refusals() {
    let program = program(&format!(
        "{SOURCE}{LATE}\nnoncomputable def noncomputablePure (x : Leaf) : Leaf := x\n"
    ));
    for root in [
        "slow",
        "unsafeLeaf",
        "noncomputablePure",
        "ffiCaller",
        "externLeaf",
        "usesForeign",
    ] {
        assert!(
            program.select_in_runtime_closure(&n(root), 0).is_err(),
            "scoped policy bypass for {root}"
        );
    }
}
