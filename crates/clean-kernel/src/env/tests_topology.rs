// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Topology tests for Environment
use super::test_helpers::{assert_bvar, pi_domain_at};
use super::tests_topology_harness::{
    assert_topological_space_decl_validation_passes, init_topological_space_env_through,
    init_topology_compact_env_through, init_topology_connected_env_through,
    init_topology_continuous_env_through, init_topology_contractible_env_through,
    init_topology_covering_space_env_through, init_topology_fundamental_group_env_through,
    init_topology_hausdorff_env_through, init_topology_homeomorphism_env_through,
    init_topology_locally_compact_env_through, init_topology_path_connected_env_through,
    init_topology_simply_connected_env_through, validate_decl_sequence_incremental_for_test,
    validate_topological_space_decls_incremental,
};
use super::*;

fn assert_sort_is_succ_param(domain: &Expr, param_name: &str, context: &str) {
    let expected = Level::succ(Level::param(Name::from_string(param_name)));
    match &domain.kind {
        ExprKind::Sort(level) => assert_eq!(
            level, &expected,
            "{context} should have binder domain Sort(Succ({param_name}))"
        ),
        _ => panic!("{context} binder domain should be Sort(Succ({param_name}))"),
    }
}

fn expect_app<'a>(expr: &'a Expr, context: &str) -> (&'a Expr, &'a Expr) {
    match &expr.kind {
        ExprKind::App(fun, arg) => (fun.as_ref(), arg.as_ref()),
        _ => panic!("{context} should be an application"),
    }
}

fn assert_path_domain_indices(domain: &Expr, alpha: u32, inst: u32, x: u32, y: u32, context: &str) {
    let (path_app3, y_expr) = expect_app(domain, context);
    assert_bvar(y_expr, y, context);
    let (path_app2, x_expr) = expect_app(path_app3, context);
    assert_bvar(x_expr, x, context);
    let (path_app1, inst_expr) = expect_app(path_app2, context);
    assert_bvar(inst_expr, inst, context);
    let (path_const, alpha_expr) = expect_app(path_app1, context);
    assert_bvar(alpha_expr, alpha, context);
    match &path_const.kind {
        ExprKind::Const(name, _) => assert_eq!(
            name,
            &Name::from_string("Topology.Path"),
            "{context} should apply Topology.Path"
        ),
        _ => panic!("{context} should apply Topology.Path"),
    }
}

fn assert_arrow_domain_body_bvars(domain: &Expr, dom: u32, body: u32, context: &str) {
    match &domain.kind {
        ExprKind::Pi(_, arg_ty, body_ty) => {
            assert_bvar(arg_ty, dom, &format!("{context} domain"));
            assert_bvar(body_ty, body, &format!("{context} body"));
        }
        _ => panic!("{context} should be a function type (Pi)"),
    }
}

/// Count the number of outermost Pi binders in an expression.
fn count_pi_binders(expr: &Expr) -> usize {
    let mut count = 0;
    let mut current = expr;
    while let ExprKind::Pi(_, _, body) = &current.kind {
        count += 1;
        current = body.as_ref();
    }
    count
}

/// Assert that a constant exists with the expected level parameter count and Pi binder count.
fn check_const_arity(
    env: &Environment,
    name: &str,
    expected_level_params: usize,
    expected_pi_binders: usize,
) -> Result<(), String> {
    let info = env
        .get_const(&Name::from_string(name))
        .ok_or_else(|| format!("{name}: not found in environment"))?;
    if info.level_params.len() != expected_level_params {
        return Err(format!(
            "{name}: expected {expected_level_params} level param(s), got {}",
            info.level_params.len()
        ));
    }
    let actual_binders = count_pi_binders(&info.type_);
    if actual_binders != expected_pi_binders {
        return Err(format!(
            "{name}: expected {expected_pi_binders} Pi binder(s), got {actual_binders}"
        ));
    }
    Ok(())
}

fn assert_const_arity(
    env: &Environment,
    name: &str,
    expected_level_params: usize,
    expected_pi_binders: usize,
) {
    check_const_arity(env, name, expected_level_params, expected_pi_binders)
        .expect("invariant: constant should exist with expected arity");
}

// ================================================================
// TopologicalSpace Tests
// ================================================================

#[test]
fn test_topological_space_init() {
    assert_topological_space_decl_validation_passes(false);

    let mut env = Environment::new();
    env.init_topological_space().unwrap();

    // Verify core declarations have correct arity (level params, Pi binders)
    assert_const_arity(&env, "TopologicalSpace", 1, 1);
    assert_const_arity(&env, "IsOpen", 1, 3);
    assert_const_arity(&env, "IsClosed", 1, 3);
    // Check flag
    assert!(env.has_topological_space());
}

#[test]
fn test_topological_space_idempotent() {
    let mut env = Environment::new();
    env.init_topological_space().unwrap();
    env.init_topological_space().unwrap(); // Should succeed without error
}

#[test]
fn test_topological_space_env_through_isolates_target_gate() {
    let env = init_topological_space_env_through("IsOpen.inter", false);
    assert_const_arity(&env, "IsOpen.inter", 1, 6);
    assert!(
        env.get_const(&Name::from_string("IsOpen.union")).is_none(),
        "env_through should stop at target and avoid downstream declarations"
    );
}

#[test]
fn test_topological_space_decl_validation_error_format_prefixes_decl_name() {
    for (name, error) in validate_topological_space_decls_incremental(false) {
        if let Some(message) = error {
            let expected_prefix = format!("{name}:");
            assert!(
                message.starts_with(&expected_prefix),
                "expected error to start with declaration name prefix `{expected_prefix}`, got `{message}`"
            );
        }
    }
}

#[test]
fn test_topological_space_decl_validation_collects_multiple_failures() {
    let invalid_decl = |decl_name: &str| Declaration::Axiom {
        name: Name::from_string(decl_name),
        level_params: vec![],
        type_: Expr::bvar(0),
    };

    let results = validate_decl_sequence_incremental_for_test(vec![
        invalid_decl("TopologyHarness.bad_1"),
        invalid_decl("TopologyHarness.bad_2"),
    ]);
    let failures: Vec<String> = results.iter().filter_map(|(_, err)| err.clone()).collect();

    assert_eq!(
        failures.len(),
        2,
        "expected both invalid declarations to fail"
    );
    assert!(failures[0].contains("TopologyHarness.bad_1"));
    assert!(failures[1].contains("TopologyHarness.bad_2"));
}

#[test]
fn test_topological_space_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("TopologicalSpace", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // TopologicalSpace : Type u → Type u
    let topo_space = Expr::const_(Name::from_string("TopologicalSpace"), vec![u_level.clone()]);
    let ty = tc.infer_type(&topo_space).unwrap();

    // Check it's a Pi type (Type u → Type u)
    assert!(
        matches!(&ty.kind, ExprKind::Pi(..)),
        "TopologicalSpace should be a Pi type"
    );
}

#[test]
fn test_is_open_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("IsOpen", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // IsOpen : {α : Type u} → [TopologicalSpace α] → (α → Prop) → Prop
    let is_open = Expr::const_(Name::from_string("IsOpen"), vec![u_level.clone()]);
    let ty = tc.infer_type(&is_open).unwrap();

    // Check it's a Pi type with 3 binders (α, inst, s)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 3, "IsOpen should have 3 Pi binders");
}

#[test]
fn test_is_closed_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("IsClosed", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // IsClosed : {α : Type u} → [TopologicalSpace α] → (α → Prop) → Prop
    let is_closed = Expr::const_(Name::from_string("IsClosed"), vec![u_level.clone()]);
    let ty = tc.infer_type(&is_closed).unwrap();

    // Check it's a Pi type with 3 binders (α, inst, s)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 3, "IsClosed should have 3 Pi binders");
}

#[test]
fn test_is_open_univ_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("IsOpen.univ", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // IsOpen.univ : {α : Type u} → [TopologicalSpace α] → IsOpen (fun _ => True)
    let is_open_univ = Expr::const_(Name::from_string("IsOpen.univ"), vec![u_level.clone()]);
    let ty = tc.infer_type(&is_open_univ).unwrap();

    // Check it's a Pi type with 2 binders (α, inst)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 2, "IsOpen.univ should have 2 Pi binders");
}

#[test]
fn test_is_open_empty_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("IsOpen.empty", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // IsOpen.empty : {α : Type u} → [TopologicalSpace α] → IsOpen (fun _ => False)
    let is_open_empty = Expr::const_(Name::from_string("IsOpen.empty"), vec![u_level.clone()]);
    let ty = tc.infer_type(&is_open_empty).unwrap();

    // Check it's a Pi type with 2 binders (α, inst)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 2, "IsOpen.empty should have 2 Pi binders");
}

#[test]
fn test_is_open_inter_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("IsOpen.inter", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // IsOpen.inter : {α : Type u} → [TopologicalSpace α] →
    //   {s t : α → Prop} → IsOpen s → IsOpen t → IsOpen (fun x => s x ∧ t x)
    let is_open_inter = Expr::const_(Name::from_string("IsOpen.inter"), vec![u_level.clone()]);
    let ty = tc.infer_type(&is_open_inter).unwrap();

    // Check it's a Pi type with 6 binders (α, inst, s, t, hs, ht)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 6, "IsOpen.inter should have 6 Pi binders");
}

#[test]
fn test_is_open_union_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("IsOpen.union", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let v = Name::from_string("v");
    let u_level = Level::param(u.clone());
    let v_level = Level::param(v.clone());

    // IsOpen.union : {α : Type u} → [TopologicalSpace α] →
    //   {ι : Type v} → {U : ι → α → Prop} → (∀ i, IsOpen (U i)) →
    //   IsOpen (fun x => ∃ i, U i x)
    let is_open_union = Expr::const_(
        Name::from_string("IsOpen.union"),
        vec![u_level.clone(), v_level.clone()],
    );
    let ty = tc.infer_type(&is_open_union).unwrap();

    // Check it's a Pi type with 5 binders (α, inst, ι, U, hU)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 5, "IsOpen.union should have 5 Pi binders");

    let iota_domain =
        pi_domain_at(&ty, 2).expect("IsOpen.union should expose ι binder as the third Pi domain");
    assert_sort_is_succ_param(iota_domain, "v", "IsOpen.union {ι : Type v}");
}

#[test]
fn test_is_closed_compl_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("IsClosed.compl", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // IsClosed.compl : {α : Type u} → [TopologicalSpace α] →
    //   {s : α → Prop} → IsClosed s ↔ IsOpen (fun x => ¬ s x)
    let is_closed_compl = Expr::const_(Name::from_string("IsClosed.compl"), vec![u_level.clone()]);
    let ty = tc.infer_type(&is_closed_compl).unwrap();

    // Check it's a Pi type with 3 binders (α, inst, s), result is Iff
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 3, "IsClosed.compl should have 3 Pi binders");
}

#[test]
fn test_topology_interior_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("Topology.Interior", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Topology.Interior : {α : Type u} → [TopologicalSpace α] →
    //   (α → Prop) → (α → Prop)
    let interior = Expr::const_(
        Name::from_string("Topology.Interior"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&interior).unwrap();

    // Check it's a Pi type with 4 binders (α, inst, s, and result α → Prop)
    // The result type (α → Prop) is itself a Pi type, so we count 4 total
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 4,
        "Topology.Interior should have 4 Pi binders (3 args + result)"
    );
}

#[test]
fn test_topology_closure_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("Topology.Closure", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Topology.Closure : {α : Type u} → [TopologicalSpace α] →
    //   (α → Prop) → (α → Prop)
    let closure = Expr::const_(Name::from_string("Topology.Closure"), vec![u_level.clone()]);
    let ty = tc.infer_type(&closure).unwrap();

    // Check it's a Pi type with 4 binders (α, inst, s, and result α → Prop)
    // The result type (α → Prop) is itself a Pi type, so we count 4 total
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 4,
        "Topology.Closure should have 4 Pi binders (3 args + result)"
    );
}

#[test]
fn test_topology_interior_spec_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("Topology.interior_spec", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Topology.interior_spec : {α : Type u} → [TopologicalSpace α] →
    //   {s : α → Prop} → (x : α) →
    //   Interior s x ↔ ∃ U, IsOpen U ∧ U x ∧ (∀ y, U y → s y)
    let interior_spec = Expr::const_(
        Name::from_string("Topology.interior_spec"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&interior_spec).unwrap();

    // Check it's a Pi type with 4 binders (α, inst, s, x)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 4, "Topology.interior_spec should have 4 Pi binders");
}

#[test]
fn test_topology_closure_spec_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("Topology.closure_spec", false);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Topology.closure_spec : {α : Type u} → [TopologicalSpace α] →
    //   {s : α → Prop} → (x : α) →
    //   Closure s x ↔ ∀ U, IsOpen U → U x → ∃ y, U y ∧ s y
    let closure_spec = Expr::const_(
        Name::from_string("Topology.closure_spec"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&closure_spec).unwrap();

    // Check it's a Pi type with 4 binders (α, inst, s, x)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(count, 4, "Topology.closure_spec should have 4 Pi binders");
}

#[test]
fn test_metric_to_topology_type() {
    use crate::tc::TypeChecker;
    let env = init_topological_space_env_through("Topology.metric_to_topology", true);

    // Verify existence and arity before deeper type-check
    assert_const_arity(&env, "Topology.metric_to_topology", 1, 2);

    let tc = TypeChecker::new(&env);
    let u = Name::from_string("u");
    let u_level = Level::param(u.clone());

    // Topology.metric_to_topology : {α : Type u} → MetricSpace α → TopologicalSpace α
    let metric_to_topo = Expr::const_(
        Name::from_string("Topology.metric_to_topology"),
        vec![u_level.clone()],
    );
    let ty = tc.infer_type(&metric_to_topo).unwrap();

    // Check it's a Pi type with 2 binders (α, inst)
    let mut count = 0;
    let mut t = ty.clone();
    while let ExprKind::Pi(_, _, body) = &t.kind {
        count += 1;
        t = body.as_ref().clone();
    }
    assert_eq!(
        count, 2,
        "Topology.metric_to_topology should have 2 Pi binders"
    );
}

#[test]
fn test_topological_space_without_metric_space() {
    // Test that TopologicalSpace can be initialized without MetricSpace
    let env = init_topological_space_env_through("Topology.closure_spec", false);

    // metric_to_topology should NOT exist because MetricSpace wasn't initialized
    assert!(
        env.get_const(&Name::from_string("Topology.metric_to_topology"))
            .is_none(),
        "Topology.metric_to_topology should NOT exist when MetricSpace is not available"
    );

    // Verify all other topology constants exist with correct arity
    assert_const_arity(&env, "TopologicalSpace", 1, 1);
    assert_const_arity(&env, "IsOpen", 1, 3);
    assert_const_arity(&env, "IsClosed", 1, 3);
    assert_const_arity(&env, "IsOpen.univ", 1, 2);
    assert_const_arity(&env, "IsOpen.empty", 1, 2);
    assert_const_arity(&env, "IsOpen.inter", 1, 6);
    assert_const_arity(&env, "IsOpen.union", 2, 5);
    assert_const_arity(&env, "IsClosed.compl", 1, 3);
    assert_const_arity(&env, "Topology.Interior", 1, 4);
    assert_const_arity(&env, "Topology.Closure", 1, 4);
    assert_const_arity(&env, "Topology.interior_spec", 1, 4);
    assert_const_arity(&env, "Topology.closure_spec", 1, 4);
}

#[test]
fn test_all_topological_space_constants() {
    let env = init_topological_space_env_through("Topology.metric_to_topology", true);

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("TopologicalSpace", 1, 1),
        ("IsOpen", 1, 3),
        ("IsClosed", 1, 3),
        ("IsOpen.univ", 1, 2),
        ("IsOpen.empty", 1, 2),
        ("IsOpen.inter", 1, 6),
        ("IsOpen.union", 2, 5),
        ("IsClosed.compl", 1, 3),
        ("Topology.Interior", 1, 4),
        ("Topology.Closure", 1, 4),
        ("Topology.interior_spec", 1, 4),
        ("Topology.closure_spec", 1, 4),
        ("Topology.metric_to_topology", 1, 2),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "TopologicalSpace constant arity failures:\n{}",
        failures.join("\n")
    );
}

// ================================================================
// Topology.Continuous tests
// ================================================================

#[test]
fn test_topology_continuous_init() {
    let mut env = Environment::new();
    env.init_topology_continuous().unwrap();
    assert!(env.has_topology_continuous());
}

#[test]
fn test_topology_continuous_idempotent() {
    let mut env = Environment::new();
    env.init_topology_continuous().unwrap();
    env.init_topology_continuous().unwrap(); // Should succeed without error
    assert!(env.has_topology_continuous());
}

#[test]
fn test_topology_continuous_type() {
    let env = init_topology_continuous_env_through("Topology.Continuous", false);

    // Count Pi binders
    let continuous_info = env
        .get_const(&Name::from_string("Topology.Continuous"))
        .unwrap();
    let mut count = 0;
    let mut ty = &continuous_info.type_;
    while let ExprKind::Pi(_, _, body) = &ty.kind {
        count += 1;
        ty = body.as_ref();
    }
    assert_eq!(
        count, 5,
        "Topology.Continuous should have 5 Pi binders (α, β, instα, instβ, f)"
    );
}

#[test]
fn test_topology_continuous_def_type() {
    let env = init_topology_continuous_env_through("Topology.continuous_def", false);
    // 5 binders: α, β, instα, instβ, f
    assert_const_arity(&env, "Topology.continuous_def", 2, 5);
}

#[test]
fn test_topology_continuous_id_type() {
    let env = init_topology_continuous_env_through("Topology.continuous_id", false);
    // {α : Type u} → [TopologicalSpace α] → Continuous id — 2 binders
    assert_const_arity(&env, "Topology.continuous_id", 1, 2);
}

#[test]
fn test_topology_continuous_const_type() {
    let env = init_topology_continuous_env_through("Topology.continuous_const", false);
    // α, β, instα, instβ, c — 5 binders, 2 level params [u, v]
    assert_const_arity(&env, "Topology.continuous_const", 2, 5);
}

#[test]
fn test_topology_continuous_comp_type() {
    let env = init_topology_continuous_env_through("Topology.continuous_comp", false);
    // {α} {β} {γ} [instα] [instβ] [instγ] (f) (g) (hf) (hg) → result
    assert_const_arity(&env, "Topology.continuous_comp", 3, 10);

    // Verify third universe parameter γ : Type w
    let comp_info = env
        .get_const(&Name::from_string("Topology.continuous_comp"))
        .unwrap();
    let gamma_domain = pi_domain_at(&comp_info.type_, 2)
        .expect("Topology.continuous_comp should expose {γ : Type w} as third Pi domain");
    assert_sort_is_succ_param(gamma_domain, "w", "Topology.continuous_comp {γ : Type w}");
}

#[test]
fn test_topology_metric_continuous_iff_with_metric() {
    let env = init_topology_continuous_env_through("Topology.metric_continuous_iff", true);
    // {α} {β} [MetricSpace α] [MetricSpace β] (f : α → β) → Iff ...
    assert_const_arity(&env, "Topology.metric_continuous_iff", 1, 5);
}

#[test]
fn test_topology_continuous_without_metric() {
    // Initialize topology continuous WITHOUT MetricSpace
    let env = init_topology_continuous_env_through("Topology.continuous_comp", false);

    // metric_continuous_iff should NOT exist because MetricSpace wasn't initialized
    assert!(
        env.get_const(&Name::from_string("Topology.metric_continuous_iff"))
            .is_none(),
        "Topology.metric_continuous_iff should NOT exist when MetricSpace is not available"
    );

    // Verify all other topology continuous constants exist with correct arity
    assert_const_arity(&env, "Topology.Continuous", 2, 5);
    assert_const_arity(&env, "Topology.continuous_def", 2, 5);
    assert_const_arity(&env, "Topology.continuous_id", 1, 2);
    assert_const_arity(&env, "Topology.continuous_const", 2, 5);
    assert_const_arity(&env, "Topology.continuous_comp", 3, 10);
}

#[test]
fn test_all_topology_continuous_constants() {
    let env = init_topology_continuous_env_through("Topology.metric_continuous_iff", true);

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.Continuous", 2, 5),
        ("Topology.continuous_def", 2, 5),
        ("Topology.continuous_id", 1, 2),
        ("Topology.continuous_const", 2, 5),
        ("Topology.continuous_comp", 3, 10),
        ("Topology.metric_continuous_iff", 1, 5),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "Continuous constant arity failures:\n{}",
        failures.join("\n")
    );
}

// =============================================================================
// Topology.Connected tests
// =============================================================================

#[test]
fn test_topology_connected_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_connected());
    env.init_topology_connected().unwrap();
    assert!(env.has_topology_connected());
}

#[test]
fn test_topology_connected_idempotent() {
    let mut env = Environment::new();
    env.init_topology_connected().unwrap();
    env.init_topology_connected().unwrap(); // Should not error
    assert!(env.has_topology_connected());
}

#[test]
fn test_topology_isclopen_type() {
    let env = init_topology_connected_env_through("Topology.IsClopen");
    // {α : Type u} → [TopologicalSpace α] → (α → Prop) → Prop
    assert_const_arity(&env, "Topology.IsClopen", 1, 3);
}

#[test]
fn test_topology_isclopen_def_type() {
    let env = init_topology_connected_env_through("Topology.isClopen_def");
    // {α : Type u} → [TopologicalSpace α] → (s : α → Prop) → Iff ...
    assert_const_arity(&env, "Topology.isClopen_def", 1, 3);
}

#[test]
fn test_topology_connected_type() {
    let env = init_topology_connected_env_through("Topology.Connected");
    // {α : Type u} → [TopologicalSpace α] → Prop — 2 binders
    assert_const_arity(&env, "Topology.Connected", 1, 2);

    // Verify result type is Prop (Sort 0)
    let info = env
        .get_const(&Name::from_string("Topology.Connected"))
        .expect("Topology.Connected should exist (verified by assert_const_arity)");
    let mut result = &info.type_;
    while let ExprKind::Pi(_, _, body) = &result.kind {
        result = body.as_ref();
    }
    assert!(
        matches!(&result.kind, ExprKind::Sort(Level::Zero)),
        "Topology.Connected result type should be Prop (Sort 0), got {:?}",
        result.kind
    );
}

#[test]
fn test_topology_connected_def_type() {
    let env = init_topology_connected_env_through("Topology.connected_def");
    // {α : Type u} → [TopologicalSpace α] → Iff ...
    assert_const_arity(&env, "Topology.connected_def", 1, 2);
}

#[test]
fn test_topology_clopen_empty_type() {
    let env = init_topology_connected_env_through("Topology.clopen_empty");
    // {α : Type u} → [TopologicalSpace α] → IsClopen (fun _ => False)
    assert_const_arity(&env, "Topology.clopen_empty", 1, 2);
}

#[test]
fn test_topology_clopen_univ_type() {
    let env = init_topology_connected_env_through("Topology.clopen_univ");
    // {α : Type u} → [TopologicalSpace α] → IsClopen (fun _ => True)
    assert_const_arity(&env, "Topology.clopen_univ", 1, 2);
}

#[test]
fn test_topology_continuous_image_connected_type() {
    let env = init_topology_connected_env_through("Topology.continuous_image_connected");
    // {α} → {β} → [instα] → [instβ] → (f) → Continuous f → Connected α → Connected β
    assert_const_arity(&env, "Topology.continuous_image_connected", 2, 7);
}

#[test]
fn test_all_topology_connected_constants() {
    let env = init_topology_connected_env_through("Topology.continuous_image_connected");

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.IsClopen", 1, 3),
        ("Topology.isClopen_def", 1, 3),
        ("Topology.Connected", 1, 2),
        ("Topology.connected_def", 1, 2),
        ("Topology.clopen_empty", 1, 2),
        ("Topology.clopen_univ", 1, 2),
        ("Topology.continuous_image_connected", 2, 7),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "Connected constant arity failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_topology_connected_dependencies_initialized() {
    // Connected should also initialize all dependencies
    let mut env = Environment::new();
    env.init_topology_connected().unwrap();

    // Check that TopologicalSpace is initialized
    assert!(env.has_topological_space());
    // Check that Continuous is initialized
    assert!(env.has_topology_continuous());
}

// =============================================================================
// Topology.Compact tests
// =============================================================================

#[test]
fn test_topology_compact_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_compact());
    env.init_topology_compact().unwrap();
    assert!(env.has_topology_compact());
}

#[test]
fn test_topology_compact_idempotent() {
    let mut env = Environment::new();
    env.init_topology_compact().unwrap();
    env.init_topology_compact().unwrap(); // Should not error
    assert!(env.has_topology_compact());
}

#[test]
fn test_topology_compact_type() {
    let env = init_topology_compact_env_through("Topology.Compact", false);
    // {α : Type u} → [TopologicalSpace α] → Prop
    assert_const_arity(&env, "Topology.Compact", 1, 2);

    // Verify result type is Prop (Sort 0)
    let info = env
        .get_const(&Name::from_string("Topology.Compact"))
        .expect("Topology.Compact should exist (verified by assert_const_arity)");
    let mut result = &info.type_;
    while let ExprKind::Pi(_, _, body) = &result.kind {
        result = body.as_ref();
    }
    assert!(
        matches!(&result.kind, ExprKind::Sort(Level::Zero)),
        "Topology.Compact result type should be Prop (Sort 0), got {:?}",
        result.kind
    );
}

#[test]
fn test_topology_compact_def_type() {
    let env = init_topology_compact_env_through("Topology.compact_def", false);
    // {α : Type u} → [TopologicalSpace α] → Iff ...
    assert_const_arity(&env, "Topology.compact_def", 1, 2);
}

#[test]
fn test_topology_is_compact_set_type() {
    let env = init_topology_compact_env_through("Topology.IsCompactSet", false);
    // {α : Type u} → [TopologicalSpace α] → (s : α → Prop) → Prop
    assert_const_arity(&env, "Topology.IsCompactSet", 1, 3);
}

#[test]
fn test_topology_compact_iff_compact_univ_type() {
    let env = init_topology_compact_env_through("Topology.compact_iff_compact_univ", false);
    // {α : Type u} → [TopologicalSpace α] → Iff ...
    assert_const_arity(&env, "Topology.compact_iff_compact_univ", 1, 2);
}

#[test]
fn test_topology_compact_closed_type() {
    let env = init_topology_compact_env_through("Topology.compact_closed", false);
    // {α} → [inst] → Compact → (s) → IsClosed s → IsCompactSet s
    assert_const_arity(&env, "Topology.compact_closed", 1, 5);
}

#[test]
fn test_topology_compact_image_type() {
    let env = init_topology_compact_env_through("Topology.compact_image", false);
    // {α} → {β} → [instα] → [instβ] → (f) → Continuous f → Compact α → Compact β
    assert_const_arity(&env, "Topology.compact_image", 2, 7);
}

#[test]
fn test_topology_compact_set_image_type() {
    let env = init_topology_compact_env_through("Topology.compact_set_image", false);
    // {α} → {β} → [instα] → [instβ] → (f) → Continuous f → (s) → IsCompactSet s → IsCompactSet ...
    assert_const_arity(&env, "Topology.compact_set_image", 2, 8);
}

#[test]
fn test_all_topology_compact_constants() {
    let env = init_topology_compact_env_through("Topology.compact_set_image", false);

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.Compact", 1, 2),
        ("Topology.compact_def", 1, 2),
        ("Topology.IsCompactSet", 1, 3),
        ("Topology.compact_iff_compact_univ", 1, 2),
        ("Topology.compact_closed", 1, 5),
        ("Topology.compact_image", 2, 7),
        ("Topology.compact_set_image", 2, 8),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "Compact constant arity failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_topology_compact_dependencies_initialized() {
    // Compact should also initialize all dependencies
    let mut env = Environment::new();
    env.init_topology_compact().unwrap();

    // Check that TopologicalSpace is initialized
    assert!(env.has_topological_space());
    // Check that Continuous is initialized
    assert!(env.has_topology_continuous());
}

#[test]
fn test_topology_metric_compact_iff_when_metric_initialized() {
    // Topology.metric_compact_iff should be added when MetricSpace and Metric.Compact
    // are initialized before Topology.Compact
    let env = init_topology_compact_env_through("Topology.metric_compact_iff", true);

    // {α : Type u} → [MetricSpace α] → Iff (Metric.Compact) (Topology.Compact)
    assert_const_arity(&env, "Topology.metric_compact_iff", 1, 2);
}

#[test]
fn test_topology_compact_without_metric() {
    // When Topology.Compact is initialized without MetricSpace,
    // metric_compact_iff should NOT be present
    let mut env = Environment::new();
    env.init_topology_compact().unwrap();

    // metric_compact_iff should NOT be available
    let info = env.get_const(&Name::from_string("Topology.metric_compact_iff"));
    assert!(
        info.is_none(),
        "Topology.metric_compact_iff should NOT exist when MetricSpace is not initialized"
    );
}

// =============================================================================
// Topology.Hausdorff tests - T2 separation axiom
// =============================================================================

#[test]
fn test_topology_hausdorff_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_hausdorff());
    env.init_topology_hausdorff().unwrap();
    assert!(env.has_topology_hausdorff());
}

#[test]
fn test_topology_hausdorff_idempotent() {
    let mut env = Environment::new();
    env.init_topology_hausdorff().unwrap();
    env.init_topology_hausdorff().unwrap(); // Should not error
    assert!(env.has_topology_hausdorff());
}

#[test]
fn test_topology_hausdorff_type() {
    // Topology.Hausdorff : {α : Type u} → [TopologicalSpace α] → Prop
    let env = init_topology_hausdorff_env_through("Topology.Hausdorff", false, false);

    let info = env
        .get_const(&Name::from_string("Topology.Hausdorff"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    // Check it's a Pi type ending in Prop
    if let ExprKind::Pi(_, _, body) = &info.type_.kind {
        if let ExprKind::Pi(_, _, inner_body) = &body.as_ref().kind {
            // Result should be Prop (Sort 0)
            if let ExprKind::Sort(Level::Zero) = &inner_body.as_ref().kind {
                // OK
            } else {
                panic!("Expected Prop (Sort 0) as result type");
            }
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type for Topology.Hausdorff");
    }
}

#[test]
fn test_topology_hausdorff_def_type() {
    let env = init_topology_hausdorff_env_through("Topology.hausdorff_def", false, false);
    assert_const_arity(&env, "Topology.hausdorff_def", 1, 2);
}

#[test]
fn test_topology_hausdorff_singleton_closed_type() {
    let env =
        init_topology_hausdorff_env_through("Topology.hausdorff_singleton_closed", false, false);
    assert_const_arity(&env, "Topology.hausdorff_singleton_closed", 1, 4);
}

#[test]
fn test_topology_hausdorff_separated_by_closed_type() {
    let env =
        init_topology_hausdorff_env_through("Topology.hausdorff_separated_by_closed", false, false);
    assert_const_arity(&env, "Topology.hausdorff_separated_by_closed", 1, 6);
}

#[test]
fn test_all_topology_hausdorff_constants() {
    // Use env_through to the last non-conditional declaration to verify all core constants
    let env =
        init_topology_hausdorff_env_through("Topology.hausdorff_separated_by_closed", false, false);

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.Hausdorff", 1, 2),
        ("Topology.hausdorff_def", 1, 2),
        ("Topology.hausdorff_singleton_closed", 1, 4),
        ("Topology.hausdorff_separated_by_closed", 1, 6),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "Hausdorff constant arity failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_topology_hausdorff_dependencies_initialized() {
    // Hausdorff should also initialize all dependencies
    let mut env = Environment::new();
    env.init_topology_hausdorff().unwrap();

    // Check that TopologicalSpace is initialized
    assert!(env.has_topological_space());
    // Check that Eq is initialized
    assert!(env.has_eq());
    // Check that Iff is initialized
    assert!(env.has_iff());
}

#[test]
fn test_topology_hausdorff_compact_closed_when_compact_initialized() {
    // Topology.hausdorff_compact_closed should be added when Topology.Compact
    // is initialized before Topology.Hausdorff
    let env = init_topology_hausdorff_env_through("Topology.hausdorff_compact_closed", true, false);
    // {α : Type u} → [TopologicalSpace α] → Hausdorff → ... → IsClosed s
    assert_const_arity(&env, "Topology.hausdorff_compact_closed", 1, 5);
}

#[test]
fn test_topology_hausdorff_without_compact() {
    // When Topology.Hausdorff is initialized without Topology.Compact,
    // hausdorff_compact_closed should NOT be present
    let mut env = Environment::new();
    env.init_topology_hausdorff().unwrap();

    // hausdorff_compact_closed should NOT be available
    let info = env.get_const(&Name::from_string("Topology.hausdorff_compact_closed"));
    assert!(
        info.is_none(),
        "Topology.hausdorff_compact_closed should NOT exist when Topology.Compact is not initialized"
    );
}

#[test]
fn test_topology_metric_hausdorff_when_metric_initialized() {
    // Topology.metric_hausdorff should be added when MetricSpace
    // is initialized before Topology.Hausdorff
    let env = init_topology_hausdorff_env_through("Topology.metric_hausdorff", false, true);
    // {α} → [MetricSpace α] → Hausdorff ...
    assert_const_arity(&env, "Topology.metric_hausdorff", 1, 2);
}

#[test]
fn test_topology_hausdorff_without_metric() {
    // When Topology.Hausdorff is initialized without MetricSpace,
    // metric_hausdorff should NOT be present
    let mut env = Environment::new();
    env.init_topology_hausdorff().unwrap();

    // metric_hausdorff should NOT be available
    let info = env.get_const(&Name::from_string("Topology.metric_hausdorff"));
    assert!(
        info.is_none(),
        "Topology.metric_hausdorff should NOT exist when MetricSpace is not initialized"
    );
}

// =============================================================================
// Topology.Homeomorphism tests
// =============================================================================

#[test]
fn test_topology_homeomorphism_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_homeomorphism());
    env.init_topology_homeomorphism().unwrap();
    assert!(env.has_topology_homeomorphism());
}

#[test]
fn test_topology_homeomorphism_idempotent() {
    let mut env = Environment::new();
    env.init_topology_homeomorphism().unwrap();
    env.init_topology_homeomorphism().unwrap();
    assert!(env.has_topology_homeomorphism());
}

#[test]
fn test_topology_homeomorphism_type() {
    // Topology.Homeomorphism : {α : Type u} → {β : Type v} →
    //   [TopologicalSpace α] → [TopologicalSpace β] →
    //   (α → β) → (β → α) → Prop
    let env = init_topology_homeomorphism_env_through("Topology.Homeomorphism", false, false);

    let info = env
        .get_const(&Name::from_string("Topology.Homeomorphism"))
        .unwrap();
    assert_eq!(info.level_params.len(), 2); // u, v

    if let ExprKind::Pi(_, _, body) = &info.type_.kind {
        if let ExprKind::Pi(_, _, inner) = &body.as_ref().kind {
            if let ExprKind::Pi(_, _, more) = &inner.as_ref().kind {
                if let ExprKind::Pi(_, _, more) = &more.as_ref().kind {
                    if let ExprKind::Pi(_, _, more) = &more.as_ref().kind {
                        if let ExprKind::Pi(_, _, result) = &more.as_ref().kind {
                            if let ExprKind::Sort(Level::Zero) = &result.as_ref().kind {
                                // OK
                            } else {
                                panic!("Expected Prop result");
                            }
                        }
                    }
                }
            }
        }
    } else {
        panic!("Expected Pi type for Topology.Homeomorphism");
    }
}

#[test]
fn test_topology_homeomorphism_def_type() {
    let env = init_topology_homeomorphism_env_through("Topology.homeomorphism_def", false, false);

    let info = env
        .get_const(&Name::from_string("Topology.homeomorphism_def"))
        .unwrap();
    assert_eq!(info.level_params.len(), 2); // u, v

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.homeomorphism_def");
    }
}

#[test]
fn test_topology_homeomorphism_id_type() {
    let env = init_topology_homeomorphism_env_through("Topology.homeomorphism_id", false, false);

    let info = env
        .get_const(&Name::from_string("Topology.homeomorphism_id"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.homeomorphism_id");
    }
}

#[test]
fn test_topology_homeomorphism_symm_type() {
    let env = init_topology_homeomorphism_env_through("Topology.homeomorphism_symm", false, false);

    let info = env
        .get_const(&Name::from_string("Topology.homeomorphism_symm"))
        .unwrap();
    assert_eq!(info.level_params.len(), 2); // u, v

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.homeomorphism_symm");
    }
}

#[test]
fn test_topology_homeomorphism_comp_type() {
    let env = init_topology_homeomorphism_env_through("Topology.homeomorphism_comp", false, false);

    let info = env
        .get_const(&Name::from_string("Topology.homeomorphism_comp"))
        .unwrap();
    assert_eq!(info.level_params.len(), 3); // u, v, w

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.homeomorphism_comp");
    }
}

#[test]
fn test_all_topology_homeomorphism_constants() {
    // Use env_through to the last non-conditional declaration to verify all core constants
    let env = init_topology_homeomorphism_env_through("Topology.homeomorphism_comp", false, false);

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.Homeomorphism", 2, 6),
        ("Topology.homeomorphism_def", 2, 6),
        ("Topology.homeomorphism_id", 1, 2),
        ("Topology.homeomorphism_symm", 2, 7),
        ("Topology.homeomorphism_comp", 3, 12),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "Homeomorphism constant arity failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_topology_homeomorphism_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_homeomorphism().unwrap();

    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
}

#[test]
fn test_topology_homeomorphism_connected_when_available() {
    // homeomorphism_connected should be added when Connected is initialized first
    let env =
        init_topology_homeomorphism_env_through("Topology.homeomorphism_connected", true, false);

    // {α} {β} [instα] [instβ] (f) (g) (homeo) (connected_α) → connected_β
    assert_const_arity(&env, "Topology.homeomorphism_connected", 2, 8);
}

#[test]
fn test_topology_homeomorphism_connected_not_added_without_dependency() {
    let mut env = Environment::new();
    env.init_topology_homeomorphism().unwrap();

    let info = env.get_const(&Name::from_string("Topology.homeomorphism_connected"));
    assert!(
        info.is_none(),
        "Topology.homeomorphism_connected should not exist without Connected initialized first"
    );
}

#[test]
fn test_topology_homeomorphism_compact_when_available() {
    let env =
        init_topology_homeomorphism_env_through("Topology.homeomorphism_compact", false, true);

    // Same shape as homeomorphism_connected but for Compact
    assert_const_arity(&env, "Topology.homeomorphism_compact", 2, 8);
}

#[test]
fn test_topology_homeomorphism_compact_not_added_without_dependency() {
    let mut env = Environment::new();
    env.init_topology_homeomorphism().unwrap();

    let info = env.get_const(&Name::from_string("Topology.homeomorphism_compact"));
    assert!(
        info.is_none(),
        "Topology.homeomorphism_compact should not exist when Compact is not initialized"
    );
}

// =============================================================================
// Topology.LocallyCompact tests
// =============================================================================

#[test]
fn test_topology_locally_compact_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_locally_compact());
    env.init_topology_locally_compact().unwrap();
    assert!(env.has_topology_locally_compact());
}

#[test]
fn test_topology_locally_compact_idempotent() {
    let mut env = Environment::new();
    env.init_topology_locally_compact().unwrap();
    env.init_topology_locally_compact().unwrap();
    assert!(env.has_topology_locally_compact());
}

#[test]
fn test_topology_locally_compact_type() {
    let env = init_topology_locally_compact_env_through("Topology.LocallyCompact");

    let info = env
        .get_const(&Name::from_string("Topology.LocallyCompact"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi(_, _, body) = &info.type_.kind {
        if let ExprKind::Pi(_, _, result) = &body.as_ref().kind {
            if let ExprKind::Sort(Level::Zero) = &result.as_ref().kind {
                // OK
            } else {
                panic!("Expected Prop result for Topology.LocallyCompact");
            }
        }
    } else {
        panic!("Expected Pi type for Topology.LocallyCompact");
    }
}

#[test]
fn test_topology_locally_compact_def_type() {
    let env = init_topology_locally_compact_env_through("Topology.locally_compact_def");

    let info = env
        .get_const(&Name::from_string("Topology.locally_compact_def"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.locally_compact_def");
    }
}

#[test]
fn test_topology_locally_compact_of_compact_type() {
    let env = init_topology_locally_compact_env_through("Topology.locally_compact_of_compact");

    let info = env
        .get_const(&Name::from_string("Topology.locally_compact_of_compact"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.locally_compact_of_compact");
    }
}

#[test]
fn test_all_topology_locally_compact_constants() {
    let env = init_topology_locally_compact_env_through("Topology.locally_compact_of_compact");

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.LocallyCompact", 1, 2),
        ("Topology.locally_compact_def", 1, 2),
        ("Topology.locally_compact_of_compact", 1, 3),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "LocallyCompact constant arity failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_topology_locally_compact_dependencies_initialized() {
    let mut env = Environment::new();
    env.init_topology_locally_compact().unwrap();

    assert!(env.has_topology_compact());
    assert!(env.has_topology_continuous());
}

// =============================================================================
// Topology.PathConnected tests
// =============================================================================

#[test]
fn test_topology_path_connected_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_path_connected());
    env.init_topology_path_connected().unwrap();
    assert!(env.has_topology_path_connected());
}

#[test]
fn test_topology_path_connected_idempotent() {
    let mut env = Environment::new();
    env.init_topology_path_connected().unwrap();
    env.init_topology_path_connected().unwrap();
    assert!(env.has_topology_path_connected());
}

#[test]
fn test_topology_unit_interval_type() {
    // Topology.UnitInterval : Type
    let env = init_topology_path_connected_env_through("Topology.UnitInterval");

    let info = env
        .get_const(&Name::from_string("Topology.UnitInterval"))
        .unwrap();
    assert_eq!(info.level_params.len(), 0);

    // Check it's Type (Sort (succ 0))
    if let ExprKind::Sort(Level::Succ(inner)) = &info.type_.kind {
        if let Level::Zero = inner.as_ref() {
            // OK - it's Type
        } else {
            panic!("Expected Type (Sort (succ zero))");
        }
    } else {
        panic!("Expected Sort for Topology.UnitInterval");
    }
}

#[test]
fn test_topology_unit_interval_endpoints() {
    // Topology.UnitInterval.zero : UnitInterval
    // Topology.UnitInterval.one : UnitInterval
    let env = init_topology_path_connected_env_through("Topology.UnitInterval.one");

    let zero_info = env
        .get_const(&Name::from_string("Topology.UnitInterval.zero"))
        .unwrap();
    let one_info = env
        .get_const(&Name::from_string("Topology.UnitInterval.one"))
        .unwrap();

    // Both should have type UnitInterval
    if let ExprKind::Const(name, _) = &zero_info.type_.kind {
        assert_eq!(name, &Name::from_string("Topology.UnitInterval"));
    } else {
        panic!("Expected Const for Topology.UnitInterval.zero type");
    }

    if let ExprKind::Const(name, _) = &one_info.type_.kind {
        assert_eq!(name, &Name::from_string("Topology.UnitInterval"));
    } else {
        panic!("Expected Const for Topology.UnitInterval.one type");
    }
}

#[test]
fn test_topology_path_type() {
    // Topology.Path : {α : Type u} → [TopologicalSpace α] → α → α → Type u
    let env = init_topology_path_connected_env_through("Topology.Path");

    let info = env.get_const(&Name::from_string("Topology.Path")).unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    // Check it's a Pi type
    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path");
    }
}

#[test]
fn test_topology_path_to_fun_type() {
    // Topology.Path.toFun : {α : Type u} → [TopologicalSpace α] →
    //   {x y : α} → Topology.Path x y → (UnitInterval → α)
    let env = init_topology_path_connected_env_through("Topology.Path.toFun");

    let info = env
        .get_const(&Name::from_string("Topology.Path.toFun"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path.toFun");
    }
}

#[test]
fn test_topology_path_continuous_type() {
    // Topology.Path.continuous : {α : Type u} → [TopologicalSpace α] →
    //   {x y : α} → (p : Topology.Path x y) → Topology.Continuous (Path.toFun p)
    let env = init_topology_path_connected_env_through("Topology.Path.continuous");

    let info = env
        .get_const(&Name::from_string("Topology.Path.continuous"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path.continuous");
    }
}

#[test]
fn test_topology_path_source_type() {
    // Topology.Path.source : {α : Type u} → [TopologicalSpace α] →
    //   {x y : α} → (p : Topology.Path x y) → Eq (Path.toFun p 0) x
    let env = init_topology_path_connected_env_through("Topology.Path.source");

    let info = env
        .get_const(&Name::from_string("Topology.Path.source"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path.source");
    }
}

#[test]
fn test_topology_path_target_type() {
    // Topology.Path.target : {α : Type u} → [TopologicalSpace α] →
    //   {x y : α} → (p : Topology.Path x y) → Eq (Path.toFun p 1) y
    let env = init_topology_path_connected_env_through("Topology.Path.target");

    let info = env
        .get_const(&Name::from_string("Topology.Path.target"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path.target");
    }
}

#[test]
fn test_topology_path_refl_type() {
    // Topology.Path.refl : {α : Type u} → [TopologicalSpace α] → (x : α) → Topology.Path x x
    let env = init_topology_path_connected_env_through("Topology.Path.refl");

    let info = env
        .get_const(&Name::from_string("Topology.Path.refl"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path.refl");
    }
}

#[test]
fn test_topology_path_symm_type() {
    // Topology.Path.symm : {α : Type u} → [TopologicalSpace α] →
    //   {x y : α} → Topology.Path x y → Topology.Path y x
    let env = init_topology_path_connected_env_through("Topology.Path.symm");

    let info = env
        .get_const(&Name::from_string("Topology.Path.symm"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path.symm");
    }
}

#[test]
fn test_topology_path_trans_type() {
    // Topology.Path.trans : {α : Type u} → [TopologicalSpace α] →
    //   {x y z : α} → Topology.Path x y → Topology.Path y z → Topology.Path x z
    let env = init_topology_path_connected_env_through("Topology.Path.trans");

    let info = env
        .get_const(&Name::from_string("Topology.Path.trans"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Path.trans");
    }
}

#[test]
fn test_topology_path_domains_use_expected_bvar_depths() {
    // Needs through Path.trans (the last Path.* constant checked)
    let env = init_topology_path_connected_env_through("Topology.Path.trans");

    for (decl_name, path_domain_binder_idx) in [
        ("Topology.Path.toFun", 4usize),
        ("Topology.Path.continuous", 4usize),
        ("Topology.Path.source", 4usize),
        ("Topology.Path.target", 4usize),
        ("Topology.Path.symm", 4usize),
    ] {
        let info = env
            .get_const(&Name::from_string(decl_name))
            .unwrap_or_else(|| panic!("{decl_name} should exist"));
        let domain = pi_domain_at(&info.type_, path_domain_binder_idx).unwrap_or_else(|| {
            panic!("{decl_name} should have Pi domain at index {path_domain_binder_idx}")
        });
        let context = format!("{decl_name} path-domain");
        assert_path_domain_indices(domain, 3, 2, 1, 0, &context);
    }

    let path_trans = env
        .get_const(&Name::from_string("Topology.Path.trans"))
        .expect("Topology.Path.trans should exist");
    let p_domain = pi_domain_at(&path_trans.type_, 5)
        .expect("Topology.Path.trans should have first path domain at Pi index 5");
    assert_path_domain_indices(p_domain, 4, 3, 2, 1, "Topology.Path.trans p-domain");

    let q_domain = pi_domain_at(&path_trans.type_, 6)
        .expect("Topology.Path.trans should have second path domain at Pi index 6");
    assert_path_domain_indices(q_domain, 5, 4, 2, 1, "Topology.Path.trans q-domain");
}

#[test]
fn test_topology_path_connected_type() {
    // Topology.PathConnected : {α : Type u} → [TopologicalSpace α] → Prop
    let env = init_topology_path_connected_env_through("Topology.PathConnected");

    let info = env
        .get_const(&Name::from_string("Topology.PathConnected"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    // Check it's a Pi type ending in Prop
    if let ExprKind::Pi(_, _, body) = &info.type_.kind {
        if let ExprKind::Pi(_, _, inner_body) = &body.as_ref().kind {
            // Result should be Prop (Sort 0)
            if let ExprKind::Sort(Level::Zero) = &inner_body.as_ref().kind {
                // OK
            } else {
                panic!("Expected Prop (Sort 0) as result type");
            }
        } else {
            panic!("Expected nested Pi type");
        }
    } else {
        panic!("Expected Pi type for Topology.PathConnected");
    }
}

#[test]
fn test_topology_path_connected_def_type() {
    // Topology.path_connected_def : {α : Type u} → [TopologicalSpace α] →
    //   Iff (PathConnected) (∀ x y, ∃ p, True)
    let env = init_topology_path_connected_env_through("Topology.path_connected_def");

    let info = env
        .get_const(&Name::from_string("Topology.path_connected_def"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.path_connected_def");
    }
}

#[test]
fn test_topology_path_connected_implies_connected_type() {
    // Topology.path_connected_implies_connected : {α : Type u} → [TopologicalSpace α] →
    //   Topology.PathConnected → Topology.Connected
    let env = init_topology_path_connected_env_through("Topology.path_connected_implies_connected");

    let info = env
        .get_const(&Name::from_string(
            "Topology.path_connected_implies_connected",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.path_connected_implies_connected");
    }
}

#[test]
fn test_topology_continuous_image_path_connected_type() {
    // Topology.continuous_image_path_connected : {α : Type u} → {β : Type v} →
    //   [TopologicalSpace α] → [TopologicalSpace β] →
    //   (f : α → β) → Topology.Continuous f → Topology.PathConnected α →
    //   Topology.PathConnected β
    let env = init_topology_path_connected_env_through("Topology.continuous_image_path_connected");

    let info = env
        .get_const(&Name::from_string(
            "Topology.continuous_image_path_connected",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 2); // u, v

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.continuous_image_path_connected");
    }

    let beta_domain = pi_domain_at(&info.type_, 1).expect(
        "Topology.continuous_image_path_connected should expose {β : Type v} as second Pi domain",
    );
    assert_sort_is_succ_param(
        beta_domain,
        "v",
        "Topology.continuous_image_path_connected {β : Type v}",
    );
}

#[test]
fn test_topology_path_connected_of_path_components_type() {
    // Topology.path_connected_of_path_components_eq : {α : Type u} → [TopologicalSpace α] →
    //   (∀ x y : α, ∃ (p : Path x y), True) → Topology.PathConnected
    let env =
        init_topology_path_connected_env_through("Topology.path_connected_of_path_components_eq");

    let info = env
        .get_const(&Name::from_string(
            "Topology.path_connected_of_path_components_eq",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.path_connected_of_path_components_eq");
    }
}

#[test]
fn test_all_topology_path_connected_constants() {
    let env =
        init_topology_path_connected_env_through("Topology.path_connected_of_path_components_eq");

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.UnitInterval", 0, 0),
        ("Topology.UnitInterval.topologicalSpace", 0, 0),
        ("Topology.UnitInterval.zero", 0, 0),
        ("Topology.UnitInterval.one", 0, 0),
        ("Topology.Path", 1, 4),
        ("Topology.Path.toFun", 1, 6),
        ("Topology.Path.continuous", 1, 5),
        ("Topology.Path.source", 1, 5),
        ("Topology.Path.target", 1, 5),
        ("Topology.Path.refl", 1, 3),
        ("Topology.Path.symm", 1, 5),
        ("Topology.Path.trans", 1, 7),
        ("Topology.PathConnected", 1, 2),
        ("Topology.path_connected_def", 1, 2),
        ("Topology.path_connected_implies_connected", 1, 3),
        ("Topology.continuous_image_path_connected", 2, 7),
        ("Topology.path_connected_of_path_components_eq", 1, 3),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in constants {
        if let Err(msg) = check_const_arity(&env, name, lvl_params, pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "PathConnected constant arity failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_topology_path_connected_dependencies_initialized() {
    // PathConnected should also initialize all dependencies
    let mut env = Environment::new();
    env.init_topology_path_connected().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_connected());
    assert!(env.has_eq());
    assert!(env.has_iff());
    assert!(env.has_exists());
}

// ========================================================================
// Topology.SimplyConnected tests
// ========================================================================

#[test]
fn test_topology_simply_connected_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_simply_connected());
    env.init_topology_simply_connected().unwrap();
    assert!(env.has_topology_simply_connected());
}

#[test]
fn test_topology_simply_connected_idempotent() {
    let mut env = Environment::new();
    env.init_topology_simply_connected().unwrap();
    env.init_topology_simply_connected().unwrap();
    assert!(env.has_topology_simply_connected());
}

#[test]
fn test_topology_loop_type() {
    // Topology.Loop : {α : Type u} → [TopologicalSpace α] → α → Type u
    let env = init_topology_simply_connected_env_through("Topology.Loop");

    // Verify 1 level param (u) and 3 Pi binders ({α}, [inst], x)
    assert_const_arity(&env, "Topology.Loop", 1, 3);

    // First binder domain should be Sort(Succ(u)) = Type u
    let info = env
        .get_const(&Name::from_string("Topology.Loop"))
        .expect("Topology.Loop should exist after env_through");
    assert_sort_is_succ_param(
        pi_domain_at(&info.type_, 0).expect("Loop should have binder 0"),
        "u",
        "Loop binder 0",
    );
}

#[test]
fn test_topology_loop_to_path_type() {
    // Topology.Loop.toPath : {α : Type u} → [TopologicalSpace α] → {x : α} → Loop x → Path x x
    let env = init_topology_simply_connected_env_through("Topology.Loop.toPath");

    let info = env
        .get_const(&Name::from_string("Topology.Loop.toPath"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Loop.toPath");
    }
}

#[test]
fn test_topology_loop_refl_type() {
    // Topology.Loop.refl : {α : Type u} → [TopologicalSpace α] → (x : α) → Loop x
    let env = init_topology_simply_connected_env_through("Topology.Loop.refl");

    let info = env
        .get_const(&Name::from_string("Topology.Loop.refl"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Loop.refl");
    }
}

#[test]
fn test_topology_loop_symm_type() {
    // Topology.Loop.symm : {α : Type u} → [TopologicalSpace α] → {x : α} → Loop x → Loop x
    let env = init_topology_simply_connected_env_through("Topology.Loop.symm");

    let info = env
        .get_const(&Name::from_string("Topology.Loop.symm"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Loop.symm");
    }
}

#[test]
fn test_topology_loop_trans_type() {
    // Topology.Loop.trans : {α : Type u} → [TopologicalSpace α] → {x : α} → Loop x → Loop x → Loop x
    let env = init_topology_simply_connected_env_through("Topology.Loop.trans");

    let info = env
        .get_const(&Name::from_string("Topology.Loop.trans"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Loop.trans");
    }
}

#[test]
fn test_topology_homotopy_type() {
    // Topology.Homotopy : {α : Type u} → [TopologicalSpace α] → {x y : α} → Path x y → Path x y → Type u
    let env = init_topology_simply_connected_env_through("Topology.Homotopy");

    let info = env
        .get_const(&Name::from_string("Topology.Homotopy"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Homotopy");
    }
}

#[test]
fn test_topology_homotopy_refl_type() {
    // Topology.Homotopy.refl : {α : Type u} → [TopologicalSpace α] → {x y : α} → (p : Path x y) → Homotopy p p
    let env = init_topology_simply_connected_env_through("Topology.Homotopy.refl");

    let info = env
        .get_const(&Name::from_string("Topology.Homotopy.refl"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Homotopy.refl");
    }
}

#[test]
fn test_topology_homotopy_symm_type() {
    // Topology.Homotopy.symm : {α : Type u} → [TopologicalSpace α] → {x y : α} → {p q : Path x y} → Homotopy p q → Homotopy q p
    let env = init_topology_simply_connected_env_through("Topology.Homotopy.symm");

    let info = env
        .get_const(&Name::from_string("Topology.Homotopy.symm"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Homotopy.symm");
    }
}

#[test]
fn test_topology_homotopy_trans_type() {
    // Topology.Homotopy.trans : {α : Type u} → [TopologicalSpace α] → {x y : α} → {p q r : Path x y} → Homotopy p q → Homotopy q r → Homotopy p r
    let env = init_topology_simply_connected_env_through("Topology.Homotopy.trans");

    let info = env
        .get_const(&Name::from_string("Topology.Homotopy.trans"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Homotopy.trans");
    }
}

#[test]
fn test_topology_loop_homotopy_type() {
    // Topology.LoopHomotopy : {α : Type u} → [TopologicalSpace α] → {x : α} → Loop x → Loop x → Type u
    let env = init_topology_simply_connected_env_through("Topology.LoopHomotopy");

    let info = env
        .get_const(&Name::from_string("Topology.LoopHomotopy"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.LoopHomotopy");
    }
}

#[test]
fn test_topology_null_homotopic_type() {
    // Topology.NullHomotopic : {α : Type u} → [TopologicalSpace α] → {x : α} → Loop x → Prop
    let env = init_topology_simply_connected_env_through("Topology.NullHomotopic");

    let info = env
        .get_const(&Name::from_string("Topology.NullHomotopic"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.NullHomotopic");
    }
}

#[test]
fn test_topology_null_homotopic_def_type() {
    // Topology.null_homotopic_def : {α : Type u} → [TopologicalSpace α] → {x : α} → (γ : Loop x) → Iff (NullHomotopic γ) (∃ h, True)
    let env = init_topology_simply_connected_env_through("Topology.null_homotopic_def");

    let info = env
        .get_const(&Name::from_string("Topology.null_homotopic_def"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.null_homotopic_def");
    }
}

#[test]
fn test_topology_simply_connected_type() {
    // Topology.SimplyConnected : {α : Type u} → [TopologicalSpace α] → Prop
    let env = init_topology_simply_connected_env_through("Topology.SimplyConnected");

    let info = env
        .get_const(&Name::from_string("Topology.SimplyConnected"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    // Check it's a Pi type ending in Prop
    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.SimplyConnected");
    }
}

#[test]
fn test_topology_simply_connected_def_type() {
    // Topology.simply_connected_def : {α : Type u} → [TopologicalSpace α] → Iff SimplyConnected (PathConnected ∧ ∀ x γ, NullHomotopic γ)
    let env = init_topology_simply_connected_env_through("Topology.simply_connected_def");

    let info = env
        .get_const(&Name::from_string("Topology.simply_connected_def"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.simply_connected_def");
    }
}

#[test]
fn test_topology_simply_connected_implies_path_connected_type() {
    // Topology.simply_connected_implies_path_connected : {α : Type u} → [TopologicalSpace α] → SimplyConnected → PathConnected
    let env = init_topology_simply_connected_env_through(
        "Topology.simply_connected_implies_path_connected",
    );

    let info = env
        .get_const(&Name::from_string(
            "Topology.simply_connected_implies_path_connected",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.simply_connected_implies_path_connected");
    }
}

#[test]
fn test_topology_simply_connected_implies_connected_type() {
    // Topology.simply_connected_implies_connected : {α : Type u} → [TopologicalSpace α] → SimplyConnected → Connected
    let env =
        init_topology_simply_connected_env_through("Topology.simply_connected_implies_connected");

    let info = env
        .get_const(&Name::from_string(
            "Topology.simply_connected_implies_connected",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.simply_connected_implies_connected");
    }
}

#[test]
fn test_topology_null_homotopic_refl_type() {
    // Topology.null_homotopic_refl : {α : Type u} → [TopologicalSpace α] → (x : α) → NullHomotopic (Loop.refl x)
    let env = init_topology_simply_connected_env_through("Topology.null_homotopic_refl");

    let info = env
        .get_const(&Name::from_string("Topology.null_homotopic_refl"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.null_homotopic_refl");
    }
}

#[test]
fn test_topology_simply_connected_all_constants_exist() {
    // Verify all 17 SimplyConnected constants are added (load through last)
    let env = init_topology_simply_connected_env_through("Topology.null_homotopic_refl");

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.Loop", 1, 3),
        ("Topology.Loop.toPath", 1, 4),
        ("Topology.Loop.refl", 1, 3),
        ("Topology.Loop.symm", 1, 4),
        ("Topology.Loop.trans", 1, 5),
        ("Topology.Homotopy", 1, 6),
        ("Topology.Homotopy.refl", 1, 5),
        ("Topology.Homotopy.symm", 1, 7),
        ("Topology.Homotopy.trans", 1, 9),
        ("Topology.LoopHomotopy", 1, 5),
        ("Topology.NullHomotopic", 1, 4),
        ("Topology.null_homotopic_def", 1, 4),
        ("Topology.SimplyConnected", 1, 2),
        ("Topology.simply_connected_def", 1, 2),
        ("Topology.simply_connected_implies_path_connected", 1, 3),
        ("Topology.simply_connected_implies_connected", 1, 3),
        ("Topology.null_homotopic_refl", 1, 3),
    ];

    for (name, lvl_params, pi_binders) in &constants {
        assert_const_arity(&env, name, *lvl_params, *pi_binders);
    }
    assert_eq!(constants.len(), 17);
}

#[test]
fn test_topology_simply_connected_dependencies_initialized() {
    // SimplyConnected should also initialize all dependencies
    let mut env = Environment::new();
    env.init_topology_simply_connected().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_connected());
    assert!(env.has_topology_path_connected());
    assert!(env.has_eq());
    assert!(env.has_iff());
    assert!(env.has_exists());
    assert!(env.has_and());
}

// ================================================================
// Tests for Topology.Contractible
// ================================================================

#[test]
fn test_topology_contractible_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_contractible());
    env.init_topology_contractible().unwrap();
    assert!(env.has_topology_contractible());
}

#[test]
fn test_topology_contractible_idempotent() {
    let mut env = Environment::new();
    env.init_topology_contractible().unwrap();
    env.init_topology_contractible().unwrap();
    assert!(env.has_topology_contractible());
}

#[test]
fn test_topology_contraction_type() {
    // Topology.Contraction : {α : Type u} → [TopologicalSpace α] → α → Type u
    let env = init_topology_contractible_env_through("Topology.Contraction");

    // Verify 1 level param (u) and 3 Pi binders ({α}, [inst], x₀)
    assert_const_arity(&env, "Topology.Contraction", 1, 3);

    // First binder domain should be Sort(Succ(u)) = Type u
    let info = env
        .get_const(&Name::from_string("Topology.Contraction"))
        .unwrap();
    assert_sort_is_succ_param(
        pi_domain_at(&info.type_, 0).expect("Contraction should have binder 0"),
        "u",
        "Contraction binder 0",
    );
}

#[test]
fn test_topology_contraction_homotopy_type() {
    // Topology.Contraction.homotopy : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   Contraction x₀ → (UnitInterval → α → α)
    let env = init_topology_contractible_env_through("Topology.Contraction.homotopy");

    let info = env
        .get_const(&Name::from_string("Topology.Contraction.homotopy"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Contraction.homotopy");
    }
}

#[test]
fn test_topology_contraction_at_zero_type() {
    // Topology.Contraction.at_zero : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   (c : Contraction x₀) → ∀ x, Eq (Contraction.homotopy c 0 x) x
    let env = init_topology_contractible_env_through("Topology.Contraction.at_zero");

    let info = env
        .get_const(&Name::from_string("Topology.Contraction.at_zero"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Contraction.at_zero");
    }
}

#[test]
fn test_topology_contraction_at_one_type() {
    // Topology.Contraction.at_one : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   (c : Contraction x₀) → ∀ x, Eq (Contraction.homotopy c 1 x) x₀
    let env = init_topology_contractible_env_through("Topology.Contraction.at_one");

    let info = env
        .get_const(&Name::from_string("Topology.Contraction.at_one"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Contraction.at_one");
    }
}

#[test]
fn test_topology_contraction_continuous_slice_type() {
    // Topology.Contraction.continuous_slice : {α : Type u} → [TopologicalSpace α] → {x₀ : α} →
    //   (c : Contraction x₀) → ∀ t : UnitInterval, Continuous (fun x => Contraction.homotopy c t x)
    let env = init_topology_contractible_env_through("Topology.Contraction.continuous_slice");

    let info = env
        .get_const(&Name::from_string("Topology.Contraction.continuous_slice"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Contraction.continuous_slice");
    }
}

#[test]
fn test_topology_contraction_mk_type() {
    // Topology.Contraction.mk : constructor for Contraction
    let env = init_topology_contractible_env_through("Topology.Contraction.mk");

    let info = env
        .get_const(&Name::from_string("Topology.Contraction.mk"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Contraction.mk");
    }
}

#[test]
fn test_topology_contractible_type() {
    // Topology.Contractible : {α : Type u} → [TopologicalSpace α] → Prop
    let env = init_topology_contractible_env_through("Topology.Contractible");

    let info = env
        .get_const(&Name::from_string("Topology.Contractible"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.Contractible");
    }
}

#[test]
fn test_topology_contractible_def_type() {
    // Topology.contractible_def : {α : Type u} → [TopologicalSpace α] →
    //   Iff Contractible (∃ x₀ : α, Contraction x₀)
    let env = init_topology_contractible_env_through("Topology.contractible_def");

    let info = env
        .get_const(&Name::from_string("Topology.contractible_def"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.contractible_def");
    }
}

#[test]
fn test_topology_contractible_implies_simply_connected_type() {
    // Topology.contractible_implies_simply_connected :
    //   {α : Type u} → [TopologicalSpace α] → Contractible → SimplyConnected
    let env =
        init_topology_contractible_env_through("Topology.contractible_implies_simply_connected");

    let info = env
        .get_const(&Name::from_string(
            "Topology.contractible_implies_simply_connected",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.contractible_implies_simply_connected");
    }
}

#[test]
fn test_topology_contractible_implies_path_connected_type() {
    // Topology.contractible_implies_path_connected :
    //   {α : Type u} → [TopologicalSpace α] → Contractible → PathConnected
    let env =
        init_topology_contractible_env_through("Topology.contractible_implies_path_connected");

    let info = env
        .get_const(&Name::from_string(
            "Topology.contractible_implies_path_connected",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.contractible_implies_path_connected");
    }
}

#[test]
fn test_topology_contractible_implies_connected_type() {
    // Topology.contractible_implies_connected :
    //   {α : Type u} → [TopologicalSpace α] → Contractible → Connected
    let env = init_topology_contractible_env_through("Topology.contractible_implies_connected");

    let info = env
        .get_const(&Name::from_string(
            "Topology.contractible_implies_connected",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.contractible_implies_connected");
    }
}

#[test]
fn test_topology_contractible_point_type() {
    // Topology.contractible_point : {α : Type u} → [TopologicalSpace α] →
    //   Contractible → (x : α) → Contraction x
    let env = init_topology_contractible_env_through("Topology.contractible_point");

    let info = env
        .get_const(&Name::from_string("Topology.contractible_point"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.contractible_point");
    }
}

#[test]
fn test_topology_contractible_all_constants_exist() {
    // Verify all 12 Contractible constants exist (load through last)
    let env = init_topology_contractible_env_through("Topology.Contraction.mk");

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.Contraction", 1, 3),
        ("Topology.Contraction.homotopy", 1, 6),
        ("Topology.Contraction.at_zero", 1, 5),
        ("Topology.Contraction.at_one", 1, 5),
        ("Topology.Contraction.continuous_slice", 1, 5),
        ("Topology.Contraction.mk", 1, 7),
        ("Topology.Contractible", 1, 2),
        ("Topology.contractible_def", 1, 2),
        ("Topology.contractible_implies_simply_connected", 1, 3),
        ("Topology.contractible_implies_path_connected", 1, 3),
        ("Topology.contractible_implies_connected", 1, 3),
        ("Topology.contractible_point", 1, 4),
    ];

    for (name, lvl_params, pi_binders) in &constants {
        assert_const_arity(&env, name, *lvl_params, *pi_binders);
    }
}

#[test]
fn test_topology_contractible_dependencies_initialized() {
    // Contractible should also initialize all dependencies
    let mut env = Environment::new();
    env.init_topology_contractible().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_connected());
    assert!(env.has_topology_path_connected());
    assert!(env.has_topology_simply_connected());
    assert!(env.has_eq());
    assert!(env.has_iff());
    assert!(env.has_exists());
}

// Tests for Topology.CoveringSpace
//
// CoveringSpace adds 16 new constants for covering space theory:
// - Fiber, fiber_def, Discrete
// - CoveringMap, CoveringMap.surjective, CoveringMap.evenly_covered,
//   CoveringMap.discrete_fiber, CoveringMap.continuous
// - EvenlyCovers
// - Lift, lift_def
// - IsCoveringSpace, is_covering_space_def
// - UniversalCover, UniversalCover.proj, UniversalCover.is_covering,
//   UniversalCover.simply_connected, UniversalCover.universal_property

#[test]
fn test_topology_covering_space_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_covering_space());
    env.init_topology_covering_space().unwrap();
    assert!(env.has_topology_covering_space());
}

#[test]
fn test_topology_covering_space_idempotent() {
    let mut env = Environment::new();
    env.init_topology_covering_space().unwrap();
    env.init_topology_covering_space().unwrap();
    assert!(env.has_topology_covering_space());
}

#[test]
fn test_topology_fiber_type() {
    // Topology.Fiber : {E B : Type u} → (E → B) → B → (E → Prop)
    let env = init_topology_covering_space_env_through("Topology.Fiber");

    // Verify 1 level param (u) and 5 Pi binders ({E}, {B}, p, b, e → Prop)
    assert_const_arity(&env, "Topology.Fiber", 1, 5);

    // First binder domain should be Sort(Succ(u)) = Type u
    let const_info = env
        .get_const(&Name::from_string("Topology.Fiber"))
        .expect("Topology.Fiber should exist");
    assert_sort_is_succ_param(
        pi_domain_at(&const_info.type_, 0).expect("Fiber should have binder 0"),
        "u",
        "Fiber binder 0",
    );
}

#[test]
fn test_topology_fiber_def_type() {
    // Topology.fiber_def : {E B : Type u} → (p : E → B) → (b : B) → (e : E) →
    //   Iff (Fiber p b e) (Eq (p e) b)
    let env = init_topology_covering_space_env_through("Topology.fiber_def");

    let const_info = env
        .get_const(&Name::from_string("Topology.fiber_def"))
        .expect("Topology.fiber_def should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.fiber_def");
    }
}

#[test]
fn test_topology_discrete_type() {
    // Topology.Discrete : {α : Type u} → (α → Prop) → Prop
    let env = init_topology_covering_space_env_through("Topology.Discrete");

    let const_info = env
        .get_const(&Name::from_string("Topology.Discrete"))
        .expect("Topology.Discrete should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.Discrete");
    }
}

#[test]
fn test_topology_covering_map_type() {
    // Topology.CoveringMap : {E B : Type u} → [TopologicalSpace E] →
    //   [TopologicalSpace B] → (E → B) → Prop
    let env = init_topology_covering_space_env_through("Topology.CoveringMap");

    let const_info = env
        .get_const(&Name::from_string("Topology.CoveringMap"))
        .expect("Topology.CoveringMap should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.CoveringMap");
    }
}

#[test]
fn test_topology_covering_space_p_arrow_indices_regression() {
    // Needs through is_covering_space_def (last CoveringMap.* declaration checked)
    let env = init_topology_covering_space_env_through("Topology.is_covering_space_def");

    // Regression for #1529/#P268: these declarations all include `(p : E -> B)` at binder 4.
    let decls = [
        "Topology.CoveringMap",
        "Topology.CoveringMap.surjective",
        "Topology.CoveringMap.evenly_covered",
        "Topology.CoveringMap.discrete_fiber",
        "Topology.CoveringMap.continuous",
        "Topology.IsCoveringSpace",
        "Topology.is_covering_space_def",
    ];

    for name in decls {
        let const_info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));
        let p_domain = pi_domain_at(&const_info.type_, 4)
            .unwrap_or_else(|| panic!("{name} should have a binder 4 domain for p : E -> B"));
        assert_arrow_domain_body_bvars(p_domain, 3, 3, &format!("{name} p : E -> B"));
    }
}

#[test]
fn test_topology_covering_map_surjective_type() {
    // Topology.CoveringMap.surjective : CoveringMap p → ∀ b, ∃ e, Eq (p e) b
    let env = init_topology_covering_space_env_through("Topology.CoveringMap.surjective");

    let const_info = env
        .get_const(&Name::from_string("Topology.CoveringMap.surjective"))
        .expect("Topology.CoveringMap.surjective should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.CoveringMap.surjective");
    }
}

#[test]
fn test_topology_evenly_covers_type() {
    // Topology.EvenlyCovers : {E B : Type u} → [TopologicalSpace E] →
    //   [TopologicalSpace B] → (E → B) → (B → Prop) → Prop
    let env = init_topology_covering_space_env_through("Topology.EvenlyCovers");

    let const_info = env
        .get_const(&Name::from_string("Topology.EvenlyCovers"))
        .expect("Topology.EvenlyCovers should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.EvenlyCovers");
    }
}

#[test]
fn test_topology_evenly_covers_u_domain_uses_b_type() {
    let env = init_topology_covering_space_env_through("Topology.EvenlyCovers");

    let const_info = env
        .get_const(&Name::from_string("Topology.EvenlyCovers"))
        .expect("Topology.EvenlyCovers should exist");

    // U binder is at index 5: `U : B -> Prop`.
    let u_domain = pi_domain_at(&const_info.type_, 5)
        .expect("Topology.EvenlyCovers should have binder 5 domain for U : B -> Prop");
    match &u_domain.kind {
        ExprKind::Pi(_, domain, body) => {
            assert_bvar(domain, 3, "Topology.EvenlyCovers U domain should use B");
            match &body.kind {
                ExprKind::Sort(level) => assert_eq!(
                    *level,
                    Level::zero(),
                    "Topology.EvenlyCovers U codomain should be Prop"
                ),
                _ => panic!("Topology.EvenlyCovers U codomain should be Prop"),
            }
        }
        _ => panic!("Topology.EvenlyCovers U binder should be a function type (Pi)"),
    }
}

#[test]
fn test_topology_covering_map_evenly_covered_type() {
    // Topology.CoveringMap.evenly_covered : CoveringMap p → ∀ b, ∃ U, ...
    let env = init_topology_covering_space_env_through("Topology.CoveringMap.evenly_covered");

    let const_info = env
        .get_const(&Name::from_string("Topology.CoveringMap.evenly_covered"))
        .expect("Topology.CoveringMap.evenly_covered should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.CoveringMap.evenly_covered");
    }
}

#[test]
fn test_topology_covering_map_discrete_fiber_type() {
    // Topology.CoveringMap.discrete_fiber : CoveringMap p → ∀ b, Discrete (Fiber p b)
    let env = init_topology_covering_space_env_through("Topology.CoveringMap.discrete_fiber");

    let const_info = env
        .get_const(&Name::from_string("Topology.CoveringMap.discrete_fiber"))
        .expect("Topology.CoveringMap.discrete_fiber should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.CoveringMap.discrete_fiber");
    }
}

#[test]
fn test_topology_lift_type() {
    // Topology.Lift : {E B X : Type} → [TopologicalSpace E] → ...
    let env = init_topology_covering_space_env_through("Topology.Lift");

    let const_info = env
        .get_const(&Name::from_string("Topology.Lift"))
        .expect("Topology.Lift should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.Lift");
    }
}

#[test]
fn test_topology_lift_arrow_indices_regression() {
    // Needs through lift_def (last Lift-related declaration checked)
    let env = init_topology_covering_space_env_through("Topology.lift_def");

    for name in ["Topology.Lift", "Topology.lift_def"] {
        let const_info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} should exist"));

        let p_domain = pi_domain_at(&const_info.type_, 6)
            .unwrap_or_else(|| panic!("{name} should have p : E -> B at binder 6"));
        assert_arrow_domain_body_bvars(p_domain, 5, 5, &format!("{name} p : E -> B"));

        let f_domain = pi_domain_at(&const_info.type_, 7)
            .unwrap_or_else(|| panic!("{name} should have f : X -> B at binder 7"));
        assert_arrow_domain_body_bvars(f_domain, 4, 6, &format!("{name} f : X -> B"));

        let ft_domain = pi_domain_at(&const_info.type_, 8)
            .unwrap_or_else(|| panic!("{name} should have f̃ : X -> E at binder 8"));
        assert_arrow_domain_body_bvars(ft_domain, 5, 8, &format!("{name} f̃ : X -> E"));
    }
}

#[test]
fn test_topology_lift_def_type() {
    // Topology.lift_def : Iff (Lift p f f̃) (∀ x, Eq (p (f̃ x)) (f x))
    let env = init_topology_covering_space_env_through("Topology.lift_def");

    let const_info = env
        .get_const(&Name::from_string("Topology.lift_def"))
        .expect("Topology.lift_def should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.lift_def");
    }
}

#[test]
fn test_topology_covering_map_continuous_type() {
    // Topology.CoveringMap.continuous : CoveringMap p → Continuous p
    let env = init_topology_covering_space_env_through("Topology.CoveringMap.continuous");

    let const_info = env
        .get_const(&Name::from_string("Topology.CoveringMap.continuous"))
        .expect("Topology.CoveringMap.continuous should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.CoveringMap.continuous");
    }
}

#[test]
fn test_topology_is_covering_space_type() {
    // Topology.IsCoveringSpace : {E B : Type u} → [TopologicalSpace E] →
    //   [TopologicalSpace B] → (E → B) → Prop
    let env = init_topology_covering_space_env_through("Topology.IsCoveringSpace");

    let const_info = env
        .get_const(&Name::from_string("Topology.IsCoveringSpace"))
        .expect("Topology.IsCoveringSpace should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.IsCoveringSpace");
    }
}

#[test]
fn test_topology_is_covering_space_def_type() {
    // Topology.is_covering_space_def : Iff (IsCoveringSpace p) (CoveringMap p)
    let env = init_topology_covering_space_env_through("Topology.is_covering_space_def");

    let const_info = env
        .get_const(&Name::from_string("Topology.is_covering_space_def"))
        .expect("Topology.is_covering_space_def should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.is_covering_space_def");
    }
}

#[test]
fn test_topology_universal_cover_type() {
    // Topology.UniversalCover : {B : Type u} → [TopologicalSpace B] →
    //   [PathConnected B] → Type u
    let env = init_topology_covering_space_env_through("Topology.UniversalCover");

    let const_info = env
        .get_const(&Name::from_string("Topology.UniversalCover"))
        .expect("Topology.UniversalCover should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.UniversalCover");
    }
}

#[test]
fn test_topology_universal_cover_proj_type() {
    // Topology.UniversalCover.proj : UniversalCover B → B
    let env = init_topology_covering_space_env_through("Topology.UniversalCover.proj");

    let const_info = env
        .get_const(&Name::from_string("Topology.UniversalCover.proj"))
        .expect("Topology.UniversalCover.proj should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.UniversalCover.proj");
    }
}

#[test]
fn test_topology_universal_cover_is_covering_type() {
    // Topology.UniversalCover.is_covering : Prop (simplified)
    let env = init_topology_covering_space_env_through("Topology.UniversalCover.is_covering");

    let const_info = env
        .get_const(&Name::from_string("Topology.UniversalCover.is_covering"))
        .expect("Topology.UniversalCover.is_covering should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.UniversalCover.is_covering");
    }
}

#[test]
fn test_topology_universal_cover_simply_connected_type() {
    // Topology.UniversalCover.simply_connected : Prop (simplified)
    let env = init_topology_covering_space_env_through("Topology.UniversalCover.simply_connected");

    let const_info = env
        .get_const(&Name::from_string(
            "Topology.UniversalCover.simply_connected",
        ))
        .expect("Topology.UniversalCover.simply_connected should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.UniversalCover.simply_connected");
    }
}

#[test]
fn test_topology_universal_cover_universal_property_type() {
    // Topology.UniversalCover.universal_property : Prop (simplified)
    let env =
        init_topology_covering_space_env_through("Topology.UniversalCover.universal_property");

    let const_info = env
        .get_const(&Name::from_string(
            "Topology.UniversalCover.universal_property",
        ))
        .expect("Topology.UniversalCover.universal_property should exist");
    if let ExprKind::Pi { .. } = &const_info.type_.kind {
        // Expected: Pi type
    } else {
        panic!("Expected Pi type for Topology.UniversalCover.universal_property");
    }
}

#[test]
fn test_topology_covering_space_all_constants_exist() {
    // Test that all 18 CoveringSpace constants exist, reporting all failures at once
    let env =
        init_topology_covering_space_env_through("Topology.UniversalCover.universal_property");

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.Fiber", 1, 5),
        ("Topology.fiber_def", 1, 5),
        ("Topology.Discrete", 1, 2),
        ("Topology.CoveringMap", 1, 5),
        ("Topology.CoveringMap.surjective", 1, 7),
        ("Topology.EvenlyCovers", 1, 6),
        ("Topology.CoveringMap.evenly_covered", 1, 7),
        ("Topology.CoveringMap.discrete_fiber", 1, 7),
        ("Topology.Lift", 2, 9),
        ("Topology.lift_def", 2, 9),
        ("Topology.CoveringMap.continuous", 1, 6),
        ("Topology.IsCoveringSpace", 1, 5),
        ("Topology.is_covering_space_def", 1, 5),
        ("Topology.UniversalCover", 1, 3),
        ("Topology.UniversalCover.proj", 1, 4),
        ("Topology.UniversalCover.is_covering", 1, 3),
        ("Topology.UniversalCover.simply_connected", 1, 3),
        ("Topology.UniversalCover.universal_property", 1, 3),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in &constants {
        if let Err(msg) = check_const_arity(&env, name, *lvl_params, *pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "CoveringSpace constant arity failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn test_topology_covering_space_dependencies_initialized() {
    // Test that initializing CoveringSpace initializes all dependencies
    let mut env = Environment::new();
    env.init_topology_covering_space().unwrap();

    // Check that all dependencies are initialized
    assert!(env.has_topological_space());
    assert!(env.has_topology_continuous());
    assert!(env.has_topology_path_connected());
    assert!(env.has_topology_homeomorphism());
    assert!(env.has_eq());
    assert!(env.has_iff());
    assert!(env.has_exists());
    assert!(env.has_and());
}

// ========================================================================
// Topology.FundamentalGroup tests
// ========================================================================

#[test]
fn test_topology_fundamental_group_init() {
    let mut env = Environment::new();
    assert!(!env.has_topology_fundamental_group());
    env.init_topology_fundamental_group().unwrap();
    assert!(env.has_topology_fundamental_group());
}

#[test]
fn test_topology_fundamental_group_idempotent() {
    let mut env = Environment::new();
    env.init_topology_fundamental_group().unwrap();
    env.init_topology_fundamental_group().unwrap();
    assert!(env.has_topology_fundamental_group());
}

#[test]
fn test_topology_fundamental_group_type() {
    // Topology.FundamentalGroup : {α : Type u} → [TopologicalSpace α] → α → Type u
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1); // u

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup");
    }
}

#[test]
fn test_topology_fundamental_group_class_type() {
    // Topology.FundamentalGroup.class : {α : Type u} → [TopologicalSpace α] → {x₀ : α} → Loop x₀ → FundamentalGroup α x₀
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.class");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.class"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.class");
    }
}

#[test]
fn test_topology_fundamental_group_class_eq_type() {
    // Topology.FundamentalGroup.class_eq : LoopHomotopy γ₁ γ₂ → Eq (class γ₁) (class γ₂)
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.class_eq");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.class_eq"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.class_eq");
    }
}

#[test]
fn test_topology_fundamental_group_mul_type() {
    // Topology.FundamentalGroup.mul : FundamentalGroup α x₀ → FundamentalGroup α x₀ → FundamentalGroup α x₀
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.mul");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.mul"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.mul");
    }
}

#[test]
fn test_topology_fundamental_group_one_type() {
    // Topology.FundamentalGroup.one : FundamentalGroup α x₀
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.one");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.one"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.one");
    }
}

#[test]
fn test_topology_fundamental_group_inv_type() {
    // Topology.FundamentalGroup.inv : FundamentalGroup α x₀ → FundamentalGroup α x₀
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.inv");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.inv"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.inv");
    }
}

#[test]
fn test_topology_fundamental_group_mul_assoc_type() {
    // Topology.FundamentalGroup.mul_assoc : ∀ a b c, Eq (mul (mul a b) c) (mul a (mul b c))
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.mul_assoc");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.mul_assoc"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.mul_assoc");
    }
}

#[test]
fn test_topology_fundamental_group_mul_one_type() {
    // Topology.FundamentalGroup.mul_one : ∀ a, Eq (mul a one) a
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.mul_one");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.mul_one"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.mul_one");
    }
}

#[test]
fn test_topology_fundamental_group_one_mul_type() {
    // Topology.FundamentalGroup.one_mul : ∀ a, Eq (mul one a) a
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.one_mul");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.one_mul"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.one_mul");
    }
}

#[test]
fn test_topology_fundamental_group_mul_inv_type() {
    // Topology.FundamentalGroup.mul_inv : ∀ a, Eq (mul a (inv a)) one
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.mul_inv");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.mul_inv"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.mul_inv");
    }
}

#[test]
fn test_topology_fundamental_group_inv_mul_type() {
    // Topology.FundamentalGroup.inv_mul : ∀ a, Eq (mul (inv a) a) one
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.inv_mul");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.inv_mul"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.inv_mul");
    }
}

#[test]
fn test_topology_fundamental_group_is_trivial_type() {
    // Topology.FundamentalGroup.IsTrivial : {α : Type u} → [TopologicalSpace α] → {x₀ : α} → Prop
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.IsTrivial");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.IsTrivial"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.IsTrivial");
    }
}

#[test]
fn test_topology_fundamental_group_trivial_def_type() {
    // Topology.FundamentalGroup.trivial_def : Iff IsTrivial (∀ g, Eq g one)
    let env = init_topology_fundamental_group_env_through("Topology.FundamentalGroup.trivial_def");

    let info = env
        .get_const(&Name::from_string("Topology.FundamentalGroup.trivial_def"))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.trivial_def");
    }
}

#[test]
fn test_topology_simply_connected_iff_trivial_pi1_type() {
    // Topology.simply_connected_iff_trivial_pi1 : PathConnected α → Iff SimplyConnected (∀ x₀, IsTrivial)
    let env =
        init_topology_fundamental_group_env_through("Topology.simply_connected_iff_trivial_pi1");

    let info = env
        .get_const(&Name::from_string(
            "Topology.simply_connected_iff_trivial_pi1",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.simply_connected_iff_trivial_pi1");
    }
}

#[test]
fn test_topology_fundamental_group_basepoint_change_type() {
    // Topology.FundamentalGroup.basepoint_change : PathConnected α → (x₀ y₀ : α) → (FG x₀ → FG y₀)
    let env =
        init_topology_fundamental_group_env_through("Topology.FundamentalGroup.basepoint_change");

    let info = env
        .get_const(&Name::from_string(
            "Topology.FundamentalGroup.basepoint_change",
        ))
        .unwrap();
    assert_eq!(info.level_params.len(), 1);

    if let ExprKind::Pi { .. } = &info.type_.kind {
        // OK
    } else {
        panic!("Expected Pi type for Topology.FundamentalGroup.basepoint_change");
    }
}

#[test]
fn test_topology_fundamental_group_all_constants_exist() {
    // Test that all 15 FundamentalGroup constants exist, reporting all failures at once
    let env =
        init_topology_fundamental_group_env_through("Topology.FundamentalGroup.basepoint_change");

    // (name, expected_level_params, expected_pi_binders)
    let constants: Vec<(&str, usize, usize)> = vec![
        ("Topology.FundamentalGroup", 1, 3),
        ("Topology.FundamentalGroup.class", 1, 4),
        ("Topology.FundamentalGroup.class_eq", 1, 6),
        ("Topology.FundamentalGroup.mul", 1, 5),
        ("Topology.FundamentalGroup.one", 1, 3),
        ("Topology.FundamentalGroup.inv", 1, 4),
        ("Topology.FundamentalGroup.mul_assoc", 1, 6),
        ("Topology.FundamentalGroup.mul_one", 1, 4),
        ("Topology.FundamentalGroup.one_mul", 1, 4),
        ("Topology.FundamentalGroup.mul_inv", 1, 4),
        ("Topology.FundamentalGroup.inv_mul", 1, 4),
        ("Topology.FundamentalGroup.IsTrivial", 1, 3),
        ("Topology.FundamentalGroup.trivial_def", 1, 3),
        ("Topology.simply_connected_iff_trivial_pi1", 1, 3),
        ("Topology.FundamentalGroup.basepoint_change", 1, 6),
    ];

    let mut failures = Vec::new();
    for (name, lvl_params, pi_binders) in &constants {
        if let Err(msg) = check_const_arity(&env, name, *lvl_params, *pi_binders) {
            failures.push(msg);
        }
    }
    assert!(
        failures.is_empty(),
        "FundamentalGroup constant arity failures:\n{}",
        failures.join("\n")
    );
}
