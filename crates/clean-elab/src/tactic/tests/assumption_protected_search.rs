// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Assumption must search with the same protected heads as checked exact.

use clean_kernel::env::{DeclarationVerification, DomainAxiomClosure};
use clean_kernel::{
    BinderInfo, ConstantKind, Environment, Expr, ExprKind, FVarId, Name, TypeChecker,
};
use clean_parser::{parse_file, SurfaceName};
use serde_json::json;

use crate::tactic::{assumption, LocalDecl, ProofState, TacticError};
use crate::unify::{MetaId, MetaState};
use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};

fn constant(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn elaborate(source: &str) -> (Environment, Result<(), ElabError>) {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let declarations = parse_file(source).expect("the authored source parses");
    assert!(!declarations.is_empty());
    for declaration in declarations {
        let processed = preprocess_decl_with_context(&declaration, &mut context);
        if let Err(error) =
            elaborate_decl_and_register_with_context(&mut env, &processed, &mut context)
        {
            return (env, Err(error));
        }
    }
    (env, Ok(()))
}

fn accepted(source: &str, name: &str, kind: ConstantKind) -> Environment {
    let (env, result) = elaborate(source);
    result.unwrap_or_else(|error| panic!("{name}: {error:?}"));
    let name = Name::from_string(name);
    let root = env.get_const(&name).expect("the authored root registers");
    assert_eq!(root.kind, kind);
    assert_eq!(
        env.declaration_verification(&name),
        Some(DeclarationVerification::FullKernelCheck)
    );
    let body = root.value.as_ref().expect("actual stored value");
    for term in [&root.type_, body] {
        assert!(!term.has_fvar_quick());
        assert!(!term.has_expr_mvar_quick());
        assert!(!term.has_level_mvar_quick());
        assert!(!term.has_loose_bvars());
    }
    assert!(!body.collect_constants().contains(&name));
    let mut checker = TypeChecker::new(&env);
    checker.set_level_params(root.level_params.clone());
    let sort = checker
        .infer_type_full(&root.type_)
        .expect("full declared type inference");
    assert!(matches!(checker.whnf(&sort).kind(), ExprKind::Sort(_)));
    checker
        .check_type(body, &root.type_)
        .expect("full stored body check");
    assert!(!checker.heartbeat_spent());
    assert!(env
        .axiom_deps(&name)
        .expect("stored axiom closure")
        .is_empty());
    assert!(env
        .foundational_axiom_deps(&name)
        .expect("foundation closure")
        .is_empty());
    assert!(DomainAxiomClosure::new()
        .assumptions_of_name(&env, &name)
        .is_empty());
    eprintln!(
        "assumption-protected-root {}",
        json!({"name":name.to_string(),"kind":format!("{kind:?}"),"type":root.type_,"value":body,"level_params":root.level_params,"full_check":true,"domain_axioms":[],"foundational_axioms":[]})
    );
    drop(checker);
    env
}

const DATA: &str = "@[irreducible] def assumption_carrier : Type := Nat\ndef assumption_data_control (good : Nat) (blocked : assumption_carrier) : Nat := by\n  assumption\n";
const PROP: &str = "@[irreducible] def assumption_gate : Prop := True\ntheorem assumption_shadowing_control (good : True) (blocked : assumption_gate) : True := by\n  assumption\n";

fn check_data(source: &str, name: &str) {
    let env = accepted(source, name, ConstantKind::Definition);
    let root = env
        .get_const(&Name::from_string(name))
        .expect("registered root");
    assert_eq!(
        root.type_,
        Expr::pi(
            BinderInfo::Default,
            constant("Nat"),
            Expr::pi(
                BinderInfo::Default,
                constant("assumption_carrier"),
                constant("Nat")
            )
        ),
        "the written parameter order/types and result are retained"
    );
    assert!(
        root.level_params.is_empty(),
        "the authored data signature is monomorphic"
    );
    let ExprKind::Pi(first, _, tail) = root.type_.kind() else {
        panic!("the first authored parameter must remain a Pi");
    };
    let ExprKind::Pi(second, _, _) = tail.kind() else {
        panic!("the second authored parameter must remain a Pi");
    };
    assert_eq!(first.info, BinderInfo::Default);
    assert_eq!(second.info, BinderInfo::Default);
    let checker = TypeChecker::new(&env);
    for (good, blocked) in [(0, 1), (7, 11)] {
        let applied = Expr::apps(
            constant(name),
            [Expr::nat_lit(good), Expr::nat_lit(blocked)],
        );
        assert!(
            !applied.has_fvar_quick()
                && !applied.has_expr_mvar_quick()
                && !applied.has_loose_bvars()
        );
        assert_eq!(
            checker
                .infer_type_full(&applied)
                .expect("full closed application inference"),
            constant("Nat")
        );
        checker
            .check_type(&applied, &constant("Nat"))
            .expect("closed application full check");
        let reduced = checker.whnf(&applied);
        assert_eq!(
            reduced,
            Expr::nat_lit(good),
            "the usable good argument must be returned"
        );
        assert!(!checker.heartbeat_spent());
        eprintln!(
            "assumption-protected-application {}",
            json!({"application":applied,"type":constant("Nat"),"whnf":reduced,"full_check":true})
        );
    }
}

#[test]
fn assumption_protected_data_selects_older_good_and_rechecks_closed_value() {
    check_data(DATA, "assumption_data_control");
}
#[test]
fn assumption_protected_prop_skips_newer_blocked() {
    accepted(PROP, "assumption_shadowing_control", ConstantKind::Theorem);
}
#[test]
fn assumption_protected_explicit_data_control() {
    check_data(
        &DATA.replace("  assumption\n", "  exact good\n"),
        "assumption_data_control",
    );
}
#[test]
fn assumption_protected_explicit_prop_control() {
    accepted(
        &PROP.replace("  assumption\n", "  exact good\n"),
        "assumption_shadowing_control",
        ConstantKind::Theorem,
    );
}
#[test]
fn assumption_protected_rwa_prop_caller() {
    accepted(
        &PROP.replace("  assumption\n", "  rwa []\n"),
        "assumption_shadowing_control",
        ConstantKind::Theorem,
    );
}
#[test]
fn assumption_protected_rwa_at_prop_refuses_blocked() {
    refuses_rewritten_local(
        &PROP.replace("  assumption\n", "  rwa [] at blocked\n"),
        "assumption_shadowing_control",
    );
}
#[test]
fn assumption_protected_rwa_data_caller() {
    check_data(
        &DATA.replace("  assumption\n", "  rwa []\n"),
        "assumption_data_control",
    );
}
#[test]
fn assumption_protected_rwa_at_data_refuses_blocked() {
    refuses_rewritten_local(
        &DATA.replace("  assumption\n", "  rwa [] at blocked\n"),
        "assumption_data_control",
    );
}
fn refuses_rewritten_local(source: &str, name: &str) {
    let (env, result) = elaborate(source);
    let error =
        result.expect_err("rwa at blocked closes with that exact local, not another assumption");
    assert!(env.get_const(&Name::from_string(name)).is_none());
    assert!(
        matches!(
            error.innermost(),
            ElabError::TacticFailed(TacticError::TypeMismatch { .. })
        ),
        "{error:?}"
    );
}

#[test]
fn assumption_protected_no_match_does_not_use_blocked_local() {
    let source="@[irreducible] def assumption_carrier : Type := Nat\ndef no_match (blocked : assumption_carrier) : Nat := by assumption\n";
    let (env, result) = elaborate(source);
    let error = result.expect_err("a protected local alone cannot solve Nat");
    assert!(env.get_const(&Name::from_string("no_match")).is_none());
    assert!(
        matches!(
            error.innermost(),
            ElabError::TacticFailed(TacticError::NoMatchingHypothesis { .. })
        ),
        "{error:?}"
    );
}

fn local(id: u64, name: &str, ty: Expr) -> LocalDecl {
    LocalDecl {
        binder_info: Default::default(),
        fvar: FVarId::new(id),
        name: SurfaceName::component(name, false),
        ty,
        value: None,
    }
}
fn conjunction(a: Expr, b: Expr) -> Expr {
    Expr::apps(constant("And"), [a, b])
}

#[test]
fn assumption_protected_preserves_most_recent_matching_local() {
    let mut state = ProofState::with_elab_context(
        Environment::with_prelude(),
        constant("Nat"),
        vec![
            local(1, "older", constant("Nat")),
            local(2, "newer", constant("Nat")),
        ],
    );
    assumption(&mut state).expect("newest actually matching local");
    assert_eq!(state.instantiated_proof(), Some(Expr::fvar(FVarId::new(2))));
}

fn meta_state(with_good: bool) -> (ProofState, MetaId) {
    let parameter = MetaId(1);
    let target = conjunction(Expr::fvar(MetaState::to_fvar(parameter)), constant("False"));
    let mut locals = Vec::new();
    if with_good {
        locals.push(local(
            1,
            "good",
            conjunction(constant("False"), constant("False")),
        ));
    }
    locals.push(local(
        2,
        "bad",
        conjunction(constant("True"), constant("True")),
    ));
    let mut state = ProofState::with_elab_context(Environment::with_prelude(), target, locals);
    assert_eq!(state.metas.fresh(Expr::prop()), parameter);
    (state, parameter)
}

#[test]
fn assumption_protected_meta_failed_candidate_rolls_back_before_older_match() {
    let (mut state, parameter) = meta_state(true);
    assumption(&mut state).expect("failed newer candidate must not pin the parameter to True");
    assert_eq!(
        state.metas.get_assignment(parameter),
        Some(&constant("False"))
    );
    assert_eq!(state.instantiated_proof(), Some(Expr::fvar(FVarId::new(1))));
    assert!(
        !state.metas.pop_scope(),
        "the candidate transaction is balanced"
    );
}

#[test]
fn assumption_protected_no_match_restores_meta_goal_and_trust() {
    let (mut state, parameter) = meta_state(false);
    let goals = format!("{:?}", state.goals());
    let trust = format!("{:?}", state.trust_ledger);
    assert!(matches!(
        assumption(&mut state),
        Err(TacticError::NoMatchingHypothesis { .. })
    ));
    assert_eq!(state.metas.get_assignment(parameter), None);
    assert_eq!(format!("{:?}", state.goals()), goals);
    assert_eq!(format!("{:?}", state.trust_ledger), trust);
    assert!(!state.metas.pop_scope());
}

#[test]
fn assumption_protected_checked_close_error_restores_meta_and_goals() {
    let mut state = ProofState::new(Environment::with_prelude(), constant("Nat"));
    state.goals.front_mut().expect("goal").local_ctx.push(local(
        1,
        "out_of_scope",
        constant("Nat"),
    ));
    let before = format!("{:?}", state.goals());
    let trust = format!("{:?}", state.trust_ledger);
    assert!(matches!(
        assumption(&mut state),
        Err(TacticError::TypeCheckFailed(_))
    ));
    assert_eq!(format!("{:?}", state.goals()), before);
    assert!(!state.metas.is_assigned(state.root_meta_id));
    assert_eq!(format!("{:?}", state.trust_ledger), trust);
    assert!(!state.metas.pop_scope());
}

#[test]
fn assumption_protected_same_carrier_is_a_real_newest_match() {
    let source = "@[irreducible] def assumption_carrier : Type := Nat\ndef same_carrier (older : assumption_carrier) (newer : assumption_carrier) : assumption_carrier := by assumption\n";
    let env = accepted(source, "same_carrier", ConstantKind::Definition);
    let checker = TypeChecker::new(&env);
    for (older, newer) in [(0, 1), (7, 11)] {
        let term = Expr::apps(
            constant("same_carrier"),
            [Expr::nat_lit(older), Expr::nat_lit(newer)],
        );
        checker
            .check_type(&term, &constant("assumption_carrier"))
            .expect("genuine closed carrier application");
        assert_eq!(checker.whnf(&term), Expr::nat_lit(newer));
    }
    assert!(!checker.heartbeat_spent());
}

#[test]
fn assumption_protected_meta_commit_waits_for_checked_close() {
    let parameter = MetaId(1);
    let target = Expr::fvar(MetaState::to_fvar(parameter));
    let mut state = ProofState::new(Environment::with_prelude(), target);
    assert_eq!(state.metas.fresh(Expr::type_()), parameter);
    state.goals.front_mut().expect("goal").local_ctx.push(local(
        1,
        "out_of_scope",
        constant("Nat"),
    ));
    let before = format!("{:?}", state.goals());
    let trust = format!("{:?}", state.trust_ledger);
    assert!(matches!(
        assumption(&mut state),
        Err(TacticError::TypeCheckFailed(_))
    ));
    assert!(state.metas.get_assignment(parameter).is_none());
    assert!(!state.metas.is_assigned(state.root_meta_id));
    assert_eq!(format!("{:?}", state.goals()), before);
    assert_eq!(format!("{:?}", state.trust_ledger), trust);
    assert!(!state.metas.pop_scope());
}

#[test]
fn assumption_protected_meta_keeps_actual_bitwise_head() {
    let env = Environment::with_prelude();
    let land_info = env
        .get_const(&Name::from_string("Nat.land"))
        .expect("real prelude operation");
    assert_eq!(land_info.kind, ConstantKind::Definition);
    assert!(
        land_info.value.is_some(),
        "do not substitute a type-only axiom"
    );
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let land = Expr::apps(constant("Nat.land"), [a, b]);
    let parameter = MetaId(1);
    let equality = |lhs, rhs| {
        Expr::apps(
            Expr::const_(
                Name::from_string("Eq"),
                vec![clean_kernel::Level::succ(clean_kernel::Level::zero())],
            ),
            [constant("Nat"), lhs, rhs],
        )
    };
    let locals = vec![
        local(1, "a", constant("Nat")),
        local(2, "b", constant("Nat")),
        local(3, "h", equality(land.clone(), land.clone())),
    ];
    let target = equality(Expr::fvar(MetaState::to_fvar(parameter)), land.clone());
    let scope = locals
        .iter()
        .map(|decl| (decl.name.clone(), decl.fvar, decl.ty.clone()))
        .collect();
    let mut state = ProofState::with_elab_context(env, target, locals);
    assert_eq!(
        state.metas.fresh_with_locals(constant("Nat"), scope),
        parameter
    );
    let original = state.current_goal().expect("goal").clone();
    let mut exact_control = state.clone();
    crate::tactic::exact(&mut exact_control, Expr::fvar(FVarId::new(3)))
        .expect("existing exact protected-head behavior");
    assert_eq!(exact_control.metas.get_assignment(parameter), Some(&land));
    assumption(&mut state).expect("the hypothesis matches through the target meta");
    assert_eq!(state.metas.get_assignment(parameter), Some(&land));
    assert!(
        matches!(state.metas.get_assignment(parameter).expect("assignment").get_app_fn().kind(), ExprKind::Const(name, _) if *name == Name::from_string("Nat.land"))
    );
    let checker = TypeChecker::with_context(state.env(), state.build_local_ctx(&original));
    checker
        .check_type(
            &state
                .instantiated_proof()
                .expect("actual chosen hypothesis"),
            &state.metas.instantiate(&original.target),
        )
        .expect("full instantiated local proof check");
    assert!(!checker.heartbeat_spent());
    drop(checker);
    assert!(!state.metas.pop_scope());
}

#[test]
fn assumption_protected_respects_speculative_ground_budget() {
    struct RestoreBudget(u32);
    impl Drop for RestoreBudget {
        fn drop(&mut self) {
            crate::tactic::core::set_speculative_tc_budget(self.0);
        }
    }
    let mut source = "def assumption_budget_0 : Type := Nat\n".to_string();
    for index in 1..48 {
        source.push_str(&format!(
            "def assumption_budget_{index} : Type := assumption_budget_{}\n",
            index - 1
        ));
    }
    let (env, result) = elaborate(&source);
    result.expect("checked alias chain");
    let mut state = ProofState::with_elab_context(
        env,
        constant("Nat"),
        vec![local(1, "h", constant("assumption_budget_47"))],
    );
    let before = format!("{:?}", state.goals());
    let restore = RestoreBudget(crate::tactic::core::set_speculative_tc_budget(1));
    let result = assumption(&mut state);
    drop(restore);
    assert!(
        result.is_err(),
        "an exhausted eligibility attempt must not close the goal"
    );
    assert_eq!(format!("{:?}", state.goals()), before);
    assert!(!state.metas.is_assigned(state.root_meta_id));
}
