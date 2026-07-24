// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the extended command elaboration module (`commands_ext`).
//!
//! Covers the command model, validation, dependency analysis, batching,
//! transformation, metrics, and integration with the kernel environment.

use std::collections::BTreeSet;

use clean_kernel::expr::FVarId;
use clean_kernel::{Declaration, Environment, Expr, Level, Name};

use crate::commands_ext::{
    analyze_command_dependencies, apply_command_transform, batch_independent_commands,
    command_dependencies, command_metrics, elaborate_command_ext, transform_command,
    validate_command, CommandBatch, CommandExtError, CommandMetrics, CommandPlan, CommandResult,
    CommandSpec, CommandTransform,
};

// =============================================================================
// Helpers
// =============================================================================

fn name(s: &str) -> Name {
    Name::from_string(s)
}

fn sort_expr() -> Expr {
    Expr::sort(Level::zero())
}

fn const_expr(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn app_expr(f: &str, a: &str) -> Expr {
    Expr::app(const_expr(f), const_expr(a))
}

fn check_cmd(expr: Expr) -> CommandSpec {
    CommandSpec::Check { expr }
}

fn eval_cmd(expr: Expr) -> CommandSpec {
    CommandSpec::Eval { expr }
}

fn print_cmd(s: &str) -> CommandSpec {
    CommandSpec::Print { name: name(s) }
}

fn plan(cmd: CommandSpec) -> CommandPlan {
    CommandPlan::new(cmd)
}

fn plan_declaring(cmd: CommandSpec, names: &[&str]) -> CommandPlan {
    CommandPlan::new(cmd).with_declares(names.iter().map(|s| name(s)))
}

// =============================================================================
// CommandSpec construction
// =============================================================================

#[test]
fn test_command_spec_check_eq() {
    let a = check_cmd(sort_expr());
    let b = check_cmd(sort_expr());
    assert_eq!(a, b);
}

#[test]
fn test_command_spec_eval_eq() {
    let a = eval_cmd(sort_expr());
    let b = eval_cmd(sort_expr());
    assert_eq!(a, b);
}

#[test]
fn test_command_spec_print_eq() {
    let a = print_cmd("Nat");
    let b = print_cmd("Nat");
    assert_eq!(a, b);
}

#[test]
fn test_command_spec_check_ne_eval() {
    let check = check_cmd(sort_expr());
    let eval = eval_cmd(sort_expr());
    assert_ne!(check, eval);
}

#[test]
fn test_command_spec_debug_format() {
    let cmd = check_cmd(sort_expr());
    let debug = format!("{cmd:?}");
    assert!(
        debug.contains("Check"),
        "Debug should mention Check variant"
    );
}

// =============================================================================
// CommandPlan construction and with_declares
// =============================================================================

#[test]
fn test_plan_new_has_empty_declares() {
    let p = plan(check_cmd(sort_expr()));
    assert!(p.declares.is_empty());
}

#[test]
fn test_plan_with_declares_adds_names() {
    let p = plan_declaring(check_cmd(sort_expr()), &["foo", "bar"]);
    assert_eq!(p.declares.len(), 2);
    assert!(p.declares.contains(&name("foo")));
    assert!(p.declares.contains(&name("bar")));
}

#[test]
fn test_plan_with_declares_deduplicates() {
    let p = plan_declaring(check_cmd(sort_expr()), &["dup", "dup"]);
    assert_eq!(p.declares.len(), 1);
}

// =============================================================================
// validate_command
// =============================================================================

#[test]
fn test_validate_check_sort_ok() {
    let cmd = check_cmd(sort_expr());
    validate_command(&cmd).expect("sort has no loose bvars or fvars");
}

#[test]
fn test_validate_eval_const_ok() {
    let cmd = eval_cmd(const_expr("Nat.zero"));
    validate_command(&cmd).expect("const has no loose bvars or fvars");
}

#[test]
fn test_validate_print_named_ok() {
    let cmd = print_cmd("Nat.add");
    validate_command(&cmd).expect("named print target is valid");
}

#[test]
fn test_validate_check_loose_bvar_err() {
    let cmd = check_cmd(Expr::bvar(0));
    let err = validate_command(&cmd).unwrap_err();
    assert_eq!(err, CommandExtError::LooseBoundVars);
}

#[test]
fn test_validate_eval_loose_bvar_err() {
    let cmd = eval_cmd(Expr::bvar(42));
    let err = validate_command(&cmd).unwrap_err();
    assert_eq!(err, CommandExtError::LooseBoundVars);
}

#[test]
fn test_validate_check_fvar_err() {
    let cmd = check_cmd(Expr::fvar(FVarId::new(1)));
    let err = validate_command(&cmd).unwrap_err();
    assert_eq!(err, CommandExtError::FreeVars);
}

#[test]
fn test_validate_eval_fvar_err() {
    let cmd = eval_cmd(Expr::fvar(FVarId::new(99)));
    let err = validate_command(&cmd).unwrap_err();
    assert_eq!(err, CommandExtError::FreeVars);
}

#[test]
fn test_validate_print_anonymous_err() {
    let cmd = CommandSpec::Print { name: Name::anon() };
    let err = validate_command(&cmd).unwrap_err();
    assert_eq!(err, CommandExtError::AnonymousPrintTarget);
}

#[test]
fn test_validate_bvar_checked_before_fvar() {
    // An expression with both loose bvars and fvars should report LooseBoundVars
    // (bvar check comes first in the implementation)
    let expr = Expr::app(Expr::bvar(0), Expr::fvar(FVarId::new(1)));
    let cmd = check_cmd(expr);
    let err = validate_command(&cmd).unwrap_err();
    assert_eq!(err, CommandExtError::LooseBoundVars);
}

// =============================================================================
// command_dependencies
// =============================================================================

#[test]
fn test_deps_check_const_single() {
    let deps = command_dependencies(&check_cmd(const_expr("Nat")));
    assert_eq!(deps.len(), 1);
    assert!(deps.contains(&name("Nat")));
}

#[test]
fn test_deps_check_app_multiple() {
    let deps = command_dependencies(&check_cmd(app_expr("f", "x")));
    assert_eq!(deps.len(), 2);
    assert!(deps.contains(&name("f")));
    assert!(deps.contains(&name("x")));
}

#[test]
fn test_deps_check_sort_empty() {
    let deps = command_dependencies(&check_cmd(sort_expr()));
    assert!(deps.is_empty());
}

#[test]
fn test_deps_eval_const() {
    let deps = command_dependencies(&eval_cmd(const_expr("Nat.zero")));
    assert_eq!(deps.len(), 1);
    assert!(deps.contains(&name("Nat.zero")));
}

#[test]
fn test_deps_print_is_name() {
    let deps = command_dependencies(&print_cmd("Nat.add"));
    assert_eq!(deps.len(), 1);
    assert!(deps.contains(&name("Nat.add")));
}

// =============================================================================
// analyze_command_dependencies
// =============================================================================

#[test]
fn test_analyze_empty_plans() {
    let infos = analyze_command_dependencies(&[]).expect("empty is fine");
    assert!(infos.is_empty());
}

#[test]
fn test_analyze_single_plan_no_deps() {
    let plans = [plan(check_cmd(sort_expr()))];
    let infos = analyze_command_dependencies(&plans).expect("should succeed");
    assert_eq!(infos.len(), 1);
    assert!(infos[0].depends_on.is_empty());
}

#[test]
fn test_analyze_detects_cross_plan_dependency() {
    let plans = [
        plan_declaring(check_cmd(sort_expr()), &["A"]),
        plan(check_cmd(const_expr("A"))),
    ];
    let infos = analyze_command_dependencies(&plans).expect("should succeed");
    assert_eq!(infos.len(), 2);
    assert!(infos[0].depends_on.is_empty(), "first declares A, no deps");
    assert!(
        infos[1].depends_on.contains(&0),
        "second references A, depends on first"
    );
}

#[test]
fn test_analyze_duplicate_declaration_err() {
    let plans = [
        plan_declaring(check_cmd(sort_expr()), &["X"]),
        plan_declaring(eval_cmd(sort_expr()), &["X"]),
    ];
    let err = analyze_command_dependencies(&plans).unwrap_err();
    match err {
        CommandExtError::DuplicateDeclaration {
            name: n,
            first,
            second,
        } => {
            assert_eq!(n, name("X"));
            assert_eq!(first, 0);
            assert_eq!(second, 1);
        }
        other => panic!("expected DuplicateDeclaration, got {other:?}"),
    }
}

#[test]
fn test_analyze_self_reference_no_self_dep() {
    // A plan that declares "A" and also references "A" should not depend on itself
    let plans = [plan_declaring(check_cmd(const_expr("A")), &["A"])];
    let infos = analyze_command_dependencies(&plans).expect("should succeed");
    assert!(infos[0].depends_on.is_empty());
}

#[test]
fn test_analyze_referenced_set_populated() {
    let plans = [plan(check_cmd(app_expr("f", "x")))];
    let infos = analyze_command_dependencies(&plans).expect("should succeed");
    assert!(infos[0].referenced.contains(&name("f")));
    assert!(infos[0].referenced.contains(&name("x")));
}

// =============================================================================
// batch_independent_commands
// =============================================================================

#[test]
fn test_batch_empty_plans() {
    let batches = batch_independent_commands(&[]).expect("empty is fine");
    assert!(batches.is_empty());
}

#[test]
fn test_batch_all_independent_single_batch() {
    let plans = [
        plan(check_cmd(sort_expr())),
        plan(eval_cmd(sort_expr())),
        plan(print_cmd("Nat")),
    ];
    let batches = batch_independent_commands(&plans).expect("no deps");
    assert_eq!(batches.len(), 1, "all independent → one batch");
    assert_eq!(batches[0].commands.len(), 3);
}

#[test]
fn test_batch_linear_chain_produces_sequential_batches() {
    // A declares "A", B depends on A and declares "B", C depends on B
    let plans = [
        plan_declaring(check_cmd(sort_expr()), &["A"]),
        plan_declaring(check_cmd(const_expr("A")), &["B"]),
        plan(check_cmd(const_expr("B"))),
    ];
    let batches = batch_independent_commands(&plans).expect("no cycle");
    assert_eq!(batches.len(), 3, "linear chain → 3 batches");
    assert_eq!(batches[0].commands, vec![0]);
    assert_eq!(batches[1].commands, vec![1]);
    assert_eq!(batches[2].commands, vec![2]);
}

#[test]
fn test_batch_diamond_dependency() {
    // A declares "A", B and C both depend on A, D depends on B and C
    let plans = [
        plan_declaring(check_cmd(sort_expr()), &["A"]),
        plan_declaring(check_cmd(const_expr("A")), &["B"]),
        plan_declaring(check_cmd(const_expr("A")), &["C"]),
        plan(check_cmd(app_expr("B", "C"))),
    ];
    let batches = batch_independent_commands(&plans).expect("no cycle");
    assert_eq!(batches.len(), 3, "diamond → 3 batches");
    assert_eq!(batches[0].commands, vec![0]);
    let batch1: BTreeSet<usize> = batches[1].commands.iter().copied().collect();
    assert!(batch1.contains(&1));
    assert!(batch1.contains(&2));
    assert_eq!(batches[2].commands, vec![3]);
}

#[test]
fn test_batch_cycle_detected() {
    // A depends on B, B depends on A
    let plans = [
        plan_declaring(check_cmd(const_expr("B")), &["A"]),
        plan_declaring(check_cmd(const_expr("A")), &["B"]),
    ];
    let err = batch_independent_commands(&plans).unwrap_err();
    match err {
        CommandExtError::DependencyCycle { cycle } => {
            assert_eq!(cycle.len(), 2);
        }
        other => panic!("expected DependencyCycle, got {other:?}"),
    }
}

#[test]
fn test_batch_indices_are_sequential() {
    let plans = [
        plan_declaring(check_cmd(sort_expr()), &["A"]),
        plan(check_cmd(const_expr("A"))),
    ];
    let batches = batch_independent_commands(&plans).expect("no cycle");
    for (i, batch) in batches.iter().enumerate() {
        assert_eq!(batch.index, i, "batch index should match position");
    }
}

// =============================================================================
// CommandTransform and apply_command_transform
// =============================================================================

#[test]
fn test_transform_normalize_strips_metadata_check() {
    let inner = const_expr("Nat");
    let with_meta = Expr::mdata(
        vec![(name("key"), clean_kernel::MDataValue::Bool(true))],
        inner,
    );
    let cmd = check_cmd(with_meta);
    let result = apply_command_transform(&cmd, &CommandTransform::NormalizeExpr);
    match &result {
        CommandSpec::Check { expr } => {
            // After normalization, metadata should be stripped
            assert_eq!(*expr, const_expr("Nat"));
        }
        _ => panic!("expected Check"),
    }
}

#[test]
fn test_transform_normalize_eval() {
    let inner = sort_expr();
    let with_meta = Expr::mdata(
        vec![(name("tag"), clean_kernel::MDataValue::Bool(false))],
        inner,
    );
    let cmd = eval_cmd(with_meta);
    let result = apply_command_transform(&cmd, &CommandTransform::NormalizeExpr);
    match &result {
        CommandSpec::Eval { expr } => {
            assert_eq!(*expr, sort_expr());
        }
        _ => panic!("expected Eval"),
    }
}

#[test]
fn test_transform_normalize_print_unchanged() {
    let cmd = print_cmd("Nat.add");
    let result = apply_command_transform(&cmd, &CommandTransform::NormalizeExpr);
    assert_eq!(result, cmd);
}

#[test]
fn test_transform_rewrite_name_check() {
    let cmd = check_cmd(const_expr("old"));
    let transform = CommandTransform::RewriteName {
        from: name("old"),
        to: name("new"),
    };
    let result = apply_command_transform(&cmd, &transform);
    match &result {
        CommandSpec::Check { expr } => {
            assert_eq!(*expr, const_expr("new"));
        }
        _ => panic!("expected Check"),
    }
}

#[test]
fn test_transform_rewrite_name_eval() {
    let cmd = eval_cmd(const_expr("old"));
    let transform = CommandTransform::RewriteName {
        from: name("old"),
        to: name("new"),
    };
    let result = apply_command_transform(&cmd, &transform);
    match &result {
        CommandSpec::Eval { expr } => {
            assert_eq!(*expr, const_expr("new"));
        }
        _ => panic!("expected Eval"),
    }
}

#[test]
fn test_transform_rewrite_name_print() {
    let cmd = print_cmd("old");
    let transform = CommandTransform::RewriteName {
        from: name("old"),
        to: name("new"),
    };
    let result = apply_command_transform(&cmd, &transform);
    assert_eq!(result, print_cmd("new"));
}

#[test]
fn test_transform_rewrite_no_match_unchanged() {
    let cmd = check_cmd(const_expr("keep"));
    let transform = CommandTransform::RewriteName {
        from: name("other"),
        to: name("replaced"),
    };
    let result = apply_command_transform(&cmd, &transform);
    match &result {
        CommandSpec::Check { expr } => {
            assert_eq!(*expr, const_expr("keep"));
        }
        _ => panic!("expected Check"),
    }
}

#[test]
fn test_transform_rewrite_in_app() {
    let cmd = check_cmd(app_expr("f", "old"));
    let transform = CommandTransform::RewriteName {
        from: name("old"),
        to: name("new"),
    };
    let result = apply_command_transform(&cmd, &transform);
    match &result {
        CommandSpec::Check { expr } => {
            assert_eq!(*expr, app_expr("f", "new"));
        }
        _ => panic!("expected Check"),
    }
}

// =============================================================================
// transform_command (multi-step)
// =============================================================================

#[test]
fn test_transform_command_empty_transforms_identity() {
    let cmd = check_cmd(const_expr("Nat"));
    let result = transform_command(&cmd, &[]);
    assert_eq!(result, cmd);
}

#[test]
fn test_transform_command_chain_two_rewrites() {
    let cmd = check_cmd(const_expr("a"));
    let transforms = [
        CommandTransform::RewriteName {
            from: name("a"),
            to: name("b"),
        },
        CommandTransform::RewriteName {
            from: name("b"),
            to: name("c"),
        },
    ];
    let result = transform_command(&cmd, &transforms);
    match &result {
        CommandSpec::Check { expr } => {
            assert_eq!(*expr, const_expr("c"));
        }
        _ => panic!("expected Check"),
    }
}

// =============================================================================
// command_metrics
// =============================================================================

#[test]
fn test_metrics_sort_expr() {
    let cmd = check_cmd(sort_expr());
    let m = command_metrics(&cmd, 1000);
    assert_eq!(m.dependency_count, 0, "sort has no deps");
    assert_eq!(m.elapsed_ns, 1000);
    assert_eq!(m.elaboration_depth, 1, "single node depth");
}

#[test]
fn test_metrics_const_expr() {
    let cmd = check_cmd(const_expr("Nat"));
    let m = command_metrics(&cmd, 500);
    assert_eq!(m.dependency_count, 1);
    assert_eq!(m.elapsed_ns, 500);
    assert_eq!(m.elaboration_depth, 1);
}

#[test]
fn test_metrics_app_expr() {
    let cmd = check_cmd(app_expr("f", "x"));
    let m = command_metrics(&cmd, 0);
    assert_eq!(m.dependency_count, 2);
    // App(Const, Const) → depth = 1 + max(1,1) = 2
    assert_eq!(m.elaboration_depth, 2);
    // nodes = 1 + 1 + 1 = 3
    assert_eq!(m.type_check_cost, 3 + 2, "3 nodes + 2 deps");
}

#[test]
fn test_metrics_print_command() {
    let cmd = print_cmd("Nat.add");
    let m = command_metrics(&cmd, 42);
    assert_eq!(m.dependency_count, 1);
    assert_eq!(m.elaboration_depth, 0, "print has no expression depth");
    assert_eq!(m.type_check_cost, 1, "print cost is always 1");
    assert_eq!(m.elapsed_ns, 42);
}

#[test]
fn test_metrics_default() {
    let m = CommandMetrics::default();
    assert_eq!(m.dependency_count, 0);
    assert_eq!(m.elaboration_depth, 0);
    assert_eq!(m.elapsed_ns, 0);
    assert_eq!(m.type_check_cost, 0);
}

// =============================================================================
// CommandExtError display and From<CommandExtError>
// =============================================================================

#[test]
fn test_error_loose_bvars_display() {
    let err = CommandExtError::LooseBoundVars;
    let msg = format!("{err}");
    assert!(msg.contains("loose bound variables"), "got: {msg}");
}

#[test]
fn test_error_free_vars_display() {
    let err = CommandExtError::FreeVars;
    let msg = format!("{err}");
    assert!(msg.contains("free variables"), "got: {msg}");
}

#[test]
fn test_error_anon_print_display() {
    let err = CommandExtError::AnonymousPrintTarget;
    let msg = format!("{err}");
    assert!(msg.contains("non-anonymous"), "got: {msg}");
}

#[test]
fn test_error_duplicate_decl_display() {
    let err = CommandExtError::DuplicateDeclaration {
        name: name("X"),
        first: 0,
        second: 1,
    };
    let msg = format!("{err}");
    assert!(msg.contains("X"), "should mention the name: {msg}");
    assert!(msg.contains("0"), "should mention first index: {msg}");
    assert!(msg.contains("1"), "should mention second index: {msg}");
}

#[test]
fn test_error_cycle_display() {
    let err = CommandExtError::DependencyCycle { cycle: vec![0, 1] };
    let msg = format!("{err}");
    assert!(msg.contains("cycle"), "got: {msg}");
}

#[test]
fn test_error_into_elab_error() {
    use crate::error::ElabError;
    let ext_err = CommandExtError::LooseBoundVars;
    let elab_err: ElabError = ext_err.into();
    match elab_err {
        ElabError::Unsupported { feature } => {
            assert!(feature.contains("loose bound variables"));
        }
        other => panic!("expected Unsupported, got {other:?}"),
    }
}

// =============================================================================
// elaborate_command_ext integration
// =============================================================================

#[test]
fn test_elaborate_check_sort_succeeds() {
    let env = Environment::new();
    let cmd = check_cmd(sort_expr());
    let exec = elaborate_command_ext(&env, &cmd, &[]).expect("sort should elaborate");
    match &exec.result {
        CommandResult::Check(_check) => {}
        other => panic!("expected Check result, got {other:?}"),
    }
    assert!(exec.dependencies.is_empty());
}

#[test]
fn test_elaborate_eval_sort_succeeds() {
    let env = Environment::new();
    let cmd = eval_cmd(sort_expr());
    let exec = elaborate_command_ext(&env, &cmd, &[]).expect("sort should eval");
    match &exec.result {
        CommandResult::Eval(_eval) => {}
        other => panic!("expected Eval result, got {other:?}"),
    }
}

#[test]
fn test_elaborate_print_registered_axiom() {
    let mut env = Environment::new();
    let decl = Declaration::Axiom {
        name: name("myAxiom"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    };
    env.add_decl(decl).expect("should register axiom");

    let cmd = print_cmd("myAxiom");
    let exec = elaborate_command_ext(&env, &cmd, &[]).expect("should print axiom");
    match &exec.result {
        CommandResult::Print(pr) => {
            assert!(pr.output.contains("myAxiom"));
        }
        other => panic!("expected Print result, got {other:?}"),
    }
    assert!(exec.dependencies.contains(&name("myAxiom")));
}

#[test]
fn test_elaborate_check_unknown_const_fails() {
    let env = Environment::new();
    let cmd = check_cmd(const_expr("nonexistent"));
    let result = elaborate_command_ext(&env, &cmd, &[]);
    assert!(result.is_err(), "unknown const should fail type inference");
}

#[test]
fn test_elaborate_with_transforms() {
    let mut env = Environment::new();
    let decl = Declaration::Axiom {
        name: name("target"),
        level_params: vec![],
        type_: Expr::sort(Level::zero()),
    };
    env.add_decl(decl).expect("should register axiom");

    // Print "source" but rewrite it to "target"
    let cmd = print_cmd("source");
    let transforms = [CommandTransform::RewriteName {
        from: name("source"),
        to: name("target"),
    }];
    let exec =
        elaborate_command_ext(&env, &cmd, &transforms).expect("should succeed after rewrite");
    match &exec.result {
        CommandResult::Print(pr) => {
            assert!(pr.output.contains("target"));
        }
        other => panic!("expected Print result, got {other:?}"),
    }
}

#[test]
fn test_elaborate_rejects_invalid_after_transform() {
    let env = Environment::new();
    let cmd = print_cmd("valid");
    // Rewrite to anonymous name (which should fail validation)
    let transforms = [CommandTransform::RewriteName {
        from: name("valid"),
        to: Name::anon(),
    }];
    let result = elaborate_command_ext(&env, &cmd, &transforms);
    assert!(result.is_err(), "anonymous print target should be rejected");
}

// =============================================================================
// CommandBatch structure
// =============================================================================

#[test]
fn test_batch_default() {
    let batch = CommandBatch::default();
    assert_eq!(batch.index, 0);
    assert!(batch.commands.is_empty());
}

// =============================================================================
// Edge cases
// =============================================================================

#[test]
fn test_nested_app_metrics_depth() {
    // app(app(sort, sort), sort) should have depth 3
    let nested = Expr::app(Expr::app(sort_expr(), sort_expr()), sort_expr());
    let cmd = check_cmd(nested);
    let m = command_metrics(&cmd, 0);
    // inner app: depth = 1 + max(1,1) = 2
    // outer app: depth = 1 + max(2,1) = 3
    assert_eq!(m.elaboration_depth, 3);
}

#[test]
fn test_lambda_metrics() {
    use clean_kernel::BinderInfo;
    let lam = Expr::lam(BinderInfo::Default, sort_expr(), const_expr("body"));
    let cmd = check_cmd(lam);
    let m = command_metrics(&cmd, 0);
    // Lam(Sort, Const) → depth = 1 + max(1,1) = 2
    assert_eq!(m.elaboration_depth, 2);
}

#[test]
fn test_pi_metrics() {
    use clean_kernel::BinderInfo;
    let pi = Expr::pi(BinderInfo::Default, sort_expr(), sort_expr());
    let cmd = check_cmd(pi);
    let m = command_metrics(&cmd, 0);
    assert_eq!(m.elaboration_depth, 2);
}

#[test]
fn test_proj_metrics() {
    let proj = Expr::proj(name("Prod"), 0, const_expr("p"));
    let cmd = check_cmd(proj);
    let m = command_metrics(&cmd, 0);
    // Proj wraps inner: depth = inner.depth + 1 = 2
    assert_eq!(m.elaboration_depth, 2);
}
