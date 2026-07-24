// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::lcnf::{Code, DeclValue};
use clean_kernel::FVarId;

fn make_test_decl(name: &str) -> Decl {
    Decl {
        name: Name::from_string(name),
        level_params: vec![],
        ty: clean_kernel::Expr::prop(),
        params: vec![],
        body: DeclValue::Code(Box::new(Code::Return(FVarId::new(0)))),
        recursive: false,
    }
}

fn identity_pass(decl: &Decl, _env: &Environment) -> Result<Vec<Decl>, PassError> {
    Ok(vec![decl.clone()])
}

#[test]
fn test_phase_ordering() {
    assert!(Phase::Base < Phase::Mono);
    assert!(Phase::Mono < Phase::Impure);
    assert!(Phase::Base < Phase::Impure);
}

#[test]
fn test_phase_to_nat() {
    assert_eq!(Phase::Base.to_nat(), 0);
    assert_eq!(Phase::Mono.to_nat(), 1);
    assert_eq!(Phase::Impure.to_nat(), 2);
}

#[test]
fn test_phase_from_nat() {
    assert_eq!(Phase::from_nat(0), Some(Phase::Base));
    assert_eq!(Phase::from_nat(1), Some(Phase::Mono));
    assert_eq!(Phase::from_nat(2), Some(Phase::Impure));
    assert_eq!(Phase::from_nat(3), None);
}

#[test]
fn test_phase_display() {
    assert_eq!(format!("{}", Phase::Base), "base");
    assert_eq!(format!("{}", Phase::Mono), "mono");
    assert_eq!(format!("{}", Phase::Impure), "impure");
}

#[test]
fn test_pass_creation() {
    let pass = Pass::new("dce", Phase::Base, identity_pass);
    assert_eq!(pass.name.to_string(), "dce");
    assert_eq!(pass.phase, Phase::Base);
    assert_eq!(pass.phase_out, Phase::Base);
    assert_eq!(pass.occurrence, 0);
}

#[test]
fn test_pass_with_transition() {
    let pass = Pass::with_transition("to_mono", Phase::Base, Phase::Mono, identity_pass);
    assert_eq!(pass.phase, Phase::Base);
    assert_eq!(pass.phase_out, Phase::Mono);
}

#[test]
fn test_pass_invalid_transition() {
    // phase_out < phase should panic
    let result = std::panic::catch_unwind(|| {
        Pass::with_transition("invalid", Phase::Mono, Phase::Base, identity_pass);
    });
    let err = result.expect_err("expected panic for invalid phase transition");
    let msg = err
        .downcast_ref::<String>()
        .map(|s| s.as_str())
        .or_else(|| err.downcast_ref::<&str>().copied())
        .unwrap_or("");
    assert!(
        msg.contains("phase_out"),
        "expected panic about phase_out, got: {msg}"
    );
}

#[test]
fn test_pass_manager_register() {
    let mut manager = PassManager::new();
    manager.register(Pass::new("dce", Phase::Base, identity_pass));
    manager.register(Pass::new("simp", Phase::Mono, identity_pass));
    manager.register(Pass::new("rc", Phase::Impure, identity_pass));

    assert_eq!(manager.passes_for_phase(Phase::Base).len(), 1);
    assert_eq!(manager.passes_for_phase(Phase::Mono).len(), 1);
    assert_eq!(manager.passes_for_phase(Phase::Impure).len(), 1);
}

#[test]
fn test_pass_manager_occurrence_tracking() {
    let mut manager = PassManager::new();
    manager.register(Pass::new("simp", Phase::Base, identity_pass));
    manager.register(Pass::new("simp", Phase::Base, identity_pass));
    manager.register(Pass::new("simp", Phase::Mono, identity_pass));

    let bounds = manager.find_occurrence_bounds(&Name::from_string("simp"));
    assert_eq!(bounds, Some((0, 2)));
}

#[test]
fn test_pass_manager_validate() {
    let mut manager = PassManager::new();
    manager.register(Pass::new("dce", Phase::Base, identity_pass));
    manager.register(Pass::new("simp", Phase::Mono, identity_pass));

    manager
        .validate()
        .expect("pass manager validation should succeed for phase-correct passes");
    assert_eq!(
        manager.pass_count(),
        2,
        "validation must not mutate registered passes"
    );
}

#[test]
fn test_phase_mismatch_error() {
    // Test that PhaseMismatch error is properly formatted
    let err = PassError::PhaseMismatch {
        expected: Phase::Base,
        actual: Phase::Mono,
    };
    let msg = format!("{}", err);
    assert!(msg.contains("base"));
    assert!(msg.contains("mono"));
    assert!(msg.contains("mismatch"));
}

#[test]
fn test_pass_manager_run() {
    let mut manager = PassManager::new();
    manager.register(Pass::new("pass1", Phase::Base, identity_pass));
    manager.register(Pass::new("pass2", Phase::Mono, identity_pass));

    let decl = make_test_decl("test");
    let env = Environment::new();

    let result = manager
        .run(&decl, &env)
        .expect("running identity passes should succeed");
    assert_eq!(
        result.len(),
        1,
        "identity passes should produce one declaration"
    );
    assert_eq!(
        result[0], decl,
        "identity passes should preserve the declaration"
    );
}

#[test]
fn test_pass_manager_run_until_phase() {
    fn mark_base(decl: &Decl, _env: &Environment) -> Result<Vec<Decl>, PassError> {
        let mut out = decl.clone();
        out.name = Name::from_string("after_base");
        Ok(vec![out])
    }

    fn mark_mono(decl: &Decl, _env: &Environment) -> Result<Vec<Decl>, PassError> {
        let mut out = decl.clone();
        out.name = Name::from_string("after_mono");
        Ok(vec![out])
    }

    fn mark_impure(decl: &Decl, _env: &Environment) -> Result<Vec<Decl>, PassError> {
        let mut out = decl.clone();
        out.name = Name::from_string("after_impure");
        Ok(vec![out])
    }

    let mut manager = PassManager::new();
    manager.register(Pass::new("base_pass", Phase::Base, mark_base));
    manager.register(Pass::new("mono_pass", Phase::Mono, mark_mono));
    manager.register(Pass::new("impure_pass", Phase::Impure, mark_impure));

    let decl = make_test_decl("test");
    let env = Environment::new();

    let base_result = manager
        .run_until_phase(&decl, &env, Phase::Base)
        .expect("base-phase run should succeed");
    assert_eq!(
        base_result[0].name,
        Name::from_string("after_base"),
        "run_until_phase(Base) must not execute mono/impure passes"
    );

    let mono_result = manager
        .run_until_phase(&decl, &env, Phase::Mono)
        .expect("mono-phase run should succeed");
    assert_eq!(
        mono_result[0].name,
        Name::from_string("after_mono"),
        "run_until_phase(Mono) must include base+mono and stop before impure"
    );

    let impure_result = manager
        .run_until_phase(&decl, &env, Phase::Impure)
        .expect("impure-phase run should succeed");
    assert_eq!(
        impure_result[0].name,
        Name::from_string("after_impure"),
        "run_until_phase(Impure) must execute all phases"
    );
}

#[test]
fn test_pass_manager_pass_count() {
    let mut manager = PassManager::new();
    assert_eq!(manager.pass_count(), 0);

    manager.register(Pass::new("p1", Phase::Base, identity_pass));
    manager.register(Pass::new("p2", Phase::Mono, identity_pass));
    assert_eq!(manager.pass_count(), 2);
}

#[test]
fn test_pass_manager_clear() {
    let mut manager = PassManager::new();
    manager.register(Pass::new("p1", Phase::Base, identity_pass));
    manager.register(Pass::new("p2", Phase::Mono, identity_pass));

    manager.clear();
    assert_eq!(manager.pass_count(), 0);
}

#[test]
fn test_default_pipeline() {
    let manager = PassManager::default_pipeline();

    // Should have lambda_lifting + to_mono + optimize + rc passes
    assert_eq!(manager.pass_count(), 4);

    // Verify base phase passes
    let base_passes = manager.passes_for_phase(Phase::Base);
    assert_eq!(base_passes.len(), 2);
    assert_eq!(base_passes[0].name.to_string(), "lambda_lifting");
    assert_eq!(base_passes[0].phase, Phase::Base);
    assert_eq!(base_passes[0].phase_out, Phase::Base);
    assert_eq!(base_passes[1].name.to_string(), "to_mono");
    assert_eq!(base_passes[1].phase, Phase::Base);
    assert_eq!(base_passes[1].phase_out, Phase::Mono);

    // Verify mono phase passes
    let mono_passes = manager.passes_for_phase(Phase::Mono);
    assert_eq!(mono_passes.len(), 2);
    assert_eq!(mono_passes[0].name.to_string(), "optimize");
    assert_eq!(mono_passes[0].phase, Phase::Mono);
    assert_eq!(mono_passes[0].phase_out, Phase::Mono);
    assert_eq!(mono_passes[1].name.to_string(), "rc");
    assert_eq!(mono_passes[1].phase, Phase::Mono);
    assert_eq!(mono_passes[1].phase_out, Phase::Impure);

    manager
        .validate()
        .expect("default pipeline should satisfy phase validation");
}

#[test]
fn test_default_pipeline_runs() {
    let manager = PassManager::default_pipeline();
    let mut decl = make_test_decl("test_fn");
    decl.level_params = vec![Name::from_string("u")];
    let env = Environment::new();

    let result = manager
        .run(&decl, &env)
        .expect("default pipeline should run on a simple declaration");
    assert!(
        !result.is_empty(),
        "default pipeline should produce at least one declaration"
    );
    assert_eq!(
        result[0].name, decl.name,
        "to_mono should preserve declaration name"
    );
    assert!(
        result[0].level_params.is_empty(),
        "to_mono should erase universe parameters in Mono phase"
    );
}

#[test]
fn test_multi_decl_pass_accumulates_auxiliary() {
    fn splitting_pass(decl: &Decl, _env: &Environment) -> Result<Vec<Decl>, PassError> {
        let aux = Decl {
            name: Name::from_string(&format!("{}_aux", decl.name)),
            ..decl.clone()
        };
        Ok(vec![decl.clone(), aux])
    }

    let mut manager = PassManager::new();
    manager.register(Pass::new("split", Phase::Base, splitting_pass));
    manager.register(Pass::new("id", Phase::Mono, identity_pass));

    let decl = make_test_decl("main");
    let env = Environment::new();

    let result = manager
        .run(&decl, &env)
        .expect("multi-decl pass should succeed");
    assert_eq!(
        result.len(),
        2,
        "splitting pass should produce main + auxiliary declaration"
    );
    assert_eq!(result[0].name.to_string(), "main");
    assert_eq!(result[1].name.to_string(), "main_aux");
}

// ═══ Spine-alignment (F2) and recursor link-honesty (F3) pipeline pins ═══

/// `Fin.ofNat` — the decl whose `Fin.mk` application carries the VALUE-level
/// inductive parameter `n` as a leading spine arg. Before the
/// spine-alignment fix, the release build silently zipped 3 args against the
/// 2-entry `Fin.mk` layout, storing the BOUND in `val`'s slot and dropping
/// `isLt` (corrupted `Fin` values).
///
/// R3 UPDATE: `Fin` is now a TRIVIAL STRUCTURE (its `isLt` field is a proof,
/// recognized through `Nat.lt`'s declared Prop codomain), so a well-formed
/// pipeline eliminates every full `Fin.mk` construction outright — the value
/// IS the bare `val`, matching the C5b scalar-carrier world where `Fin.val`
/// reads no ctor field. The pin flips: `Fin.ofNat` must compile with NO
/// `Fin.mk` cell in its final IR; any that DOES survive (e.g. a partial
/// application) must still align 1:1 with the field layout.
#[test]
fn test_fin_of_nat_compiles_with_aligned_fin_mk_fields() {
    use crate::ir::{IRBody, IRExpr};

    let env = Environment::with_prelude();
    let info = env
        .get_const(&Name::from_string("Fin.ofNat"))
        .expect("prelude has Fin.ofNat")
        .clone();
    let decl = crate::to_lcnf::constant_to_decl(&env, &info)
        .expect("Fin.ofNat lowers to LCNF")
        .expect("Fin.ofNat is not an extern");
    let arts = compile_lcnf_decls(
        std::slice::from_ref(&decl),
        &env,
        &PipelineConfig::default(),
    )
    .expect("Fin.ofNat must compile with correct field placement, not refuse");

    let mut fin_mk_ctors = 0usize;
    for ir_decl in &arts.boxed_ir_decls {
        let mut stack: Vec<&IRBody> = vec![&ir_decl.body];
        while let Some(body) = stack.pop() {
            match body {
                IRBody::VDecl { value, rest, .. } => {
                    if let IRExpr::Ctor { info, args }
                    | IRExpr::Reuse {
                        ctor: info, args, ..
                    } = value
                    {
                        if info.name.to_string() == "Fin.mk" {
                            fin_mk_ctors += 1;
                            assert_eq!(
                                args.len(),
                                info.field_types.len(),
                                "Fin.mk args must align 1:1 with its field layout"
                            );
                            assert!(
                                args.len() <= 2,
                                "Fin.mk has 2 fields; the leading param `n` must \
                                 not appear as a field arg"
                            );
                        }
                    }
                    stack.push(rest);
                }
                IRBody::JDecl {
                    body: jp_body,
                    rest,
                    ..
                } => {
                    stack.push(jp_body);
                    stack.push(rest);
                }
                IRBody::Inc { rest, .. }
                | IRBody::Dec { rest, .. }
                | IRBody::Set { rest, .. }
                | IRBody::SetTag { rest, .. }
                | IRBody::USet { rest, .. }
                | IRBody::SSet { rest, .. } => stack.push(rest),
                IRBody::Case { alts, default, .. } => {
                    for alt in alts {
                        stack.push(&alt.body);
                    }
                    if let Some(default) = default {
                        stack.push(default);
                    }
                }
                IRBody::Jmp { .. } | IRBody::Ret(_) | IRBody::Unreachable => {}
            }
        }
    }
    assert_eq!(
        fin_mk_ctors, 0,
        "Fin is a trivial structure: Fin.ofNat's final IR must not allocate \
         any Fin.mk cell (the value is the bare `val` under the C5b \
         scalar-carrier discipline)"
    );
}

/// F3 link-honesty: a declaration whose final IR references a VALUELESS
/// kernel recursor is refused even in the previously-allowed all-`Ptr`
/// shape — no runtime implements any `l_<Ind>_rec` symbol, so the old
/// "certified extern fallback" could never link.
#[test]
fn test_valueless_recursor_reference_refused_even_all_ptr() {
    use crate::lcnf::{Arg, Code, DeclValue, LetDecl, LetValue, Param};
    use clean_kernel::Expr;

    let env = Environment::with_prelude();
    assert!(
        env.get_recursor(&Name::from_string("Nat.rec")).is_some(),
        "precondition: Nat.rec is in the kernel recursor map"
    );

    // let x := Nat.rec motive z s; ret x — every operand Object-typed (the
    // all-Ptr shape the pre-fix guard certified as an extern fallback).
    let nat = || Expr::const_str("Nat");
    let decl = Decl {
        name: Name::from_string("calls_nat_rec"),
        level_params: vec![],
        ty: nat(),
        params: vec![
            Param::new(FVarId::new(0), Name::from_string("m"), nat()),
            Param::new(FVarId::new(1), Name::from_string("z"), nat()),
            Param::new(FVarId::new(2), Name::from_string("s"), nat()),
        ],
        body: DeclValue::Code(Box::new(Code::let_bind(
            LetDecl::new(
                FVarId::new(3),
                Name::from_string("x"),
                nat(),
                LetValue::Const {
                    name: Name::from_string("Nat.rec"),
                    levels: vec![],
                    args: vec![
                        Arg::FVar(FVarId::new(0)),
                        Arg::FVar(FVarId::new(1)),
                        Arg::FVar(FVarId::new(2)),
                    ],
                },
            ),
            Code::ret(FVarId::new(3)),
        ))),
        recursive: false,
    };

    let err = compile_lcnf_decls(
        std::slice::from_ref(&decl),
        &env,
        &PipelineConfig::default(),
    )
    .expect_err("valueless recursor reference must refuse (nothing can link it)");
    let msg = err.to_string();
    assert!(
        msg.contains("Nat.rec") && msg.contains("extern boundary"),
        "refusal must name the recursor and the extern-boundary demotion, got: {msg}"
    );
}
