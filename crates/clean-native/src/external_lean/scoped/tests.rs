// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use clean_kernel::env::{CompiledBefore, TrustedEnvExt};
use clean_kernel::{ConstantInfo, Expr};
use std::path::Path;

const SOURCE: &str = "prelude\nimport Target\ninductive Flag where | off | on\ndef handoff (x : Flag) : Flag := x\ndef outside (x : Flag) : Flag := x\ndef fast (x : Leaf) : Leaf := x\n@[implemented_by fast] def slow (x : Leaf) : Leaf := targetVal\ndef routed : Leaf := slow targetVal\n";
fn n(value: &str) -> Name {
    Name::from_string(value)
}
fn program(roots: &[Name]) -> Result<ExternalLeanScopedProgram, ExternalLeanError> {
    let dir = tempfile::tempdir().unwrap();
    let source = dir.path().join("Scoped.lean");
    std::fs::write(&source, SOURCE).unwrap();
    ExternalLeanScopedProgram::elaborate(
        ExternalLeanInput {
            file: &source,
            module: &n("Scoped"),
            imports: &[n("Target")],
            search_paths: &[Path::new(env!("CARGO_MANIFEST_DIR"))
                .join("../../tests/fixtures/olean/v4.30.0/closure_cache")],
            world: LeanWorld::ORACLE,
        },
        roots,
    )
}

#[test]
fn scoped_external_actual430_existing_compiler_executes_ordinary_owned_root() {
    let program = program(&[n("handoff"), n("routed")]).unwrap();
    assert!(program.source_capture().snapshot_blake3.is_some());
    assert!(program.scoped_capture().is_complete());
    assert!(!program.scoped_capture().members().contains(&n("outside")));
    for root in ["fast", "slow", "targetVal"] {
        assert!(program.scoped_capture().members().contains(&n(root)));
    }
    for selection in [
        program.select(&n("fast"), 0),
        program.select_in_runtime_closure(&n("fast"), 0),
    ] {
        assert!(
            matches!(selection, Err(ExternalLeanError::Input(ref s)) if s.contains("outside explicitly captured runtime roots"))
        );
    }
    assert!(program.inspect_owned_declaration(&n("handoff")).is_ok());
    assert!(program
        .replay_context(&[n("handoff")])
        .unwrap()
        .replay_verdict()
        .passed(false));
    // The underlying logical capture has never acquired default native usage.
    assert!(program.program.select(&n("handoff"), 0).is_err());
    assert!(program
        .program
        .select_in_runtime_closure(&n("handoff"), 0)
        .is_err());
    for selected in [
        program.select(&n("handoff"), 0),
        program.select_in_runtime_closure(&n("handoff"), 0),
    ] {
        let selected = selected.unwrap();
        assert!(selected.selection.runtime_binding_closure.is_some());
        assert!(selected.replay_verdict().passed(false));
        assert!(selected.runtime_replay_verdict().passed(false));
        let c = selected.emit(EmitFormat::C).unwrap();
        let build = tempfile::tempdir().unwrap();
        let binary = crate::native_build::build_extract_executable(build.path(), "", &c,
            "int main(void) { for (unsigned tag = 0; tag < 2; ++tag) { clean_obj* result = l_handoff(clean_box(tag)); if (clean_obj_tag(result) != tag) return 1; } return 0; }").unwrap();
        assert!(std::process::Command::new(binary)
            .status()
            .unwrap()
            .success());
    }
    let routed = program.select_in_runtime_closure(&n("routed"), 0).unwrap();
    assert!(routed.declarations().iter().any(|d| d.name == n("fast")));
    assert!(!routed.declarations().iter().any(|d| d.name == n("slow")));
    println!("actual430 scoped ordinary imported consumer: both selection policies, replay, same general C compiler and actual native execution PASS; runtime redirect captured and selected");
}

#[test]
fn scoped_external_source_ownership_requested_roots_and_foreign_custody_refuse() {
    assert!(program(&[]).is_err());
    let error = match program(&[n("targetVal")]) {
        Err(e) => e,
        Ok(_) => panic!("imported root accepted"),
    };
    assert!(error
        .to_string()
        .contains("not declared by the captured source"));
    let mut first = program(&[n("handoff")]).unwrap();
    for root in [
        n("outside"),
        n("targetVal"),
        Name::anon().str("handoff.hidden"),
    ] {
        for selected in [
            first.select(&root, 0),
            first.select_in_runtime_closure(&root, 0),
        ] {
            assert!(
                matches!(selected, Err(ExternalLeanError::Input(ref s)) if s.contains("outside explicitly captured runtime roots"))
            );
        }
    }
    let second = program(&[n("handoff")]).unwrap();
    first.scope = second.scope;
    for selected in [
        first.select(&n("handoff"), 0),
        first.select_in_runtime_closure(&n("handoff"), 0),
    ] {
        assert!(
            matches!(selected, Err(ExternalLeanError::Input(ref s)) if s.contains("different source custody"))
        );
    }
}

fn replace(program: &mut ExternalLeanScopedProgram, mutate: impl FnOnce(&mut ConstantInfo)) {
    let name = n("handoff");
    let mut info = program.program.env.get_const(&name).unwrap().clone();
    mutate(&mut info);
    program.program.env.forget_decl(&name);
    assert!(program
        .program
        .env
        .extend_constants_structural(std::iter::once(info))
        .is_empty());
}
#[test]
fn scoped_external_changed_rows_attributes_and_readiness_cannot_reuse_scope() {
    let mut changed = program(&[n("handoff")]).unwrap();
    // Valid same-type replacement still belongs to another captured source row.
    replace(&mut changed, |info| {
        info.value = Some(Expr::lam(
            clean_kernel::BinderInfo::Default,
            Expr::const_(n("Flag"), vec![]),
            Expr::const_(n("Flag.on"), vec![]),
        ))
    });
    for result in [
        changed.select(&n("handoff"), 0),
        changed.select_in_runtime_closure(&n("handoff"), 0),
    ] {
        assert!(
            matches!(result, Err(ExternalLeanError::Input(ref s)) if s.contains("scope changed"))
        );
    }
    let mut changed = program(&[n("handoff")]).unwrap();
    changed
        .program
        .env
        .register_extern(n("handoff"), "different_actual_runtime".into());
    assert!(
        matches!(changed.select(&n("handoff"), 0), Err(ExternalLeanError::Input(ref s)) if s.contains("scope changed"))
    );
    let mut changed = program(&[n("handoff")]).unwrap();
    Arc::get_mut(&mut changed.scope).unwrap().observation =
        RuntimeScopedEnvironmentCapture::capture_with_limits(
            &changed.program.base,
            &changed.program.env,
            changed.source_capture().sources.clone(),
            &discover(&changed.program, &[n("handoff")]).unwrap(),
            RuntimeSourceCaptureLimits {
                total_bytes: 1,
                ..RuntimeSourceCaptureLimits::default()
            },
        );
    for result in [
        changed.select(&n("handoff"), 0),
        changed.select_in_runtime_closure(&n("handoff"), 0),
    ] {
        assert!(
            matches!(result, Err(ExternalLeanError::Input(ref s)) if s.contains("incomplete scoped source snapshot"))
        );
    }
}

#[test]
fn scoped_external_global_binding_order_policy_is_not_relaxed() {
    let mut program = program(&[n("handoff")]).unwrap();
    program.program.env.record_compiled_before(vec![(
        n("unrelated"),
        CompiledBefore {
            rebound: n("unrelated"),
            via: n("unrelated"),
        },
    )]);
    assert!(program.select(&n("handoff"), 0).is_err());
    program.select_in_runtime_closure(&n("handoff"), 0).unwrap();
    program.program.env.record_compiled_before(vec![(
        n("handoff"),
        CompiledBefore {
            rebound: n("handoff"),
            via: n("handoff"),
        },
    )]);
    assert!(program.select_in_runtime_closure(&n("handoff"), 0).is_err());
}

#[test]
fn scoped_external_actual435_full_init_retains_global_refusal_and_captures_exact_scope() {
    let dir = tempfile::tempdir().unwrap();
    let file = dir.path().join("Scoped435.lean");
    std::fs::write(
        &file,
        "def query (x : Nat) : Nat := x\ndef outside (x : Nat) : Nat := x\n",
    )
    .unwrap();
    let program = ExternalLeanScopedProgram::elaborate(
        ExternalLeanInput {
            file: &file,
            module: &n("Scoped435"),
            imports: &[n("Init")],
            search_paths: &[],
            world: LeanWorld::Lean435,
        },
        &[n("query")],
    )
    .expect("actual435 full-Init selected scope must fit unchanged default limits");
    let global = program.source_capture();
    assert!(!global.errors.is_empty());
    assert!(!global.row_failures.is_empty());
    assert!(!global.delta_complete);
    assert!(global.snapshot_blake3.is_none());
    let scoped = program.scoped_capture();
    assert!(scoped.is_complete());
    assert!(scoped.members().contains(&n("Nat")));
    assert!(!scoped.members().contains(&n("outside")));
    assert!(program.select(&n("outside"), 0).is_err());
    assert!(program.program.select(&n("query"), 0).is_err());
    assert!(program
        .program
        .select_in_runtime_closure(&n("query"), 0)
        .is_err());
    let selected = program.select_in_runtime_closure(&n("query"), 0).unwrap();
    assert!(selected.replay_verdict().passed(false));
    assert!(selected.runtime_replay_verdict().passed(false));
    let emitted = selected.emit(EmitFormat::C).unwrap();
    assert!(emitted.contains("l_query"));
    println!("actual435 full Init: global {} row failures/{} errors, absent digest/incomplete delta preserved; exact scoped {} members under64MiBtotal/16MiBrow passes replay+selection+existing C emission; no native execution claim", global.row_failures.len(), global.errors.len(), scoped.members().len());
}
