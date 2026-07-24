// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier-prefix and skolem-dependency coverage.

use super::*;

fn make_mixed_quantifier_with_trigger() -> Expr {
    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let f_x = Expr::app(Expr::const_(Name::from_string("f"), vec![]), Expr::bvar(1));
    let eq = make_eq(ty_a.clone(), f_x, Expr::bvar(0));

    let exists_const = Expr::const_(Name::from_string("Exists"), vec![]);
    let inner_lam = Expr::lam(BinderInfo::Default, ty_a.clone(), eq);
    let inner_exists = Expr::app(Expr::app(exists_const, ty_a), inner_lam);
    Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("A"), vec![]),
        inner_exists,
    )
}

#[test]
fn test_quantifier_prefix_empty() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let p = Expr::fvar(FVarId::new(1));
    let prop = bridge.classify_prop(&p);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("non-quantified proposition should flatten");

    assert!(prefix.is_empty());
    assert_eq!(prefix.alternation_depth(), 0);
}

#[test]
fn test_quantifier_prefix_single_forall() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let p_x = Expr::app(p, Expr::bvar(0));
    let forall = Expr::pi(BinderInfo::Default, ty_a, p_x);

    let prop = bridge.classify_prop(&forall);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("single forall should flatten");

    assert_eq!(prefix.len(), 1);
    assert!(prefix.is_purely_universal());
    assert!(!prefix.is_purely_existential());
    assert_eq!(prefix.alternation_depth(), 0);
    assert_eq!(prefix.outermost_kind(), Some(QuantifierKind::Forall));
}

#[test]
fn test_quantifier_prefix_nested_forall() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let p_xy = Expr::app(Expr::app(p, Expr::bvar(1)), Expr::bvar(0));
    let inner_forall = Expr::pi(BinderInfo::Default, ty_b, p_xy);
    let outer_forall = Expr::pi(BinderInfo::Default, ty_a, inner_forall);

    let prop = bridge.classify_prop(&outer_forall);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("nested forall should flatten");

    assert_eq!(prefix.len(), 2);
    assert!(prefix.is_purely_universal());
    assert_eq!(prefix.alternation_depth(), 0);
    assert_eq!(prefix.forall_indices().len(), 2);
    assert!(prefix.exists_indices().is_empty());
}

#[test]
fn test_quantifier_prefix_forall_exists() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let p_xy = Expr::app(Expr::app(p, Expr::bvar(1)), Expr::bvar(0));

    let exists_const = Expr::const_(Name::from_string("Exists"), vec![]);
    let inner_lam = Expr::lam(BinderInfo::Default, ty_b.clone(), p_xy.clone());
    let inner_exists = Expr::app(Expr::app(exists_const, ty_b), inner_lam.clone());
    let outer_forall = Expr::pi(BinderInfo::Default, ty_a, inner_exists.clone());

    let prop = bridge.classify_prop(&outer_forall);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("forall-exists prefix should flatten");

    assert_eq!(prefix.len(), 2);
    assert!(!prefix.is_purely_universal());
    assert!(!prefix.is_purely_existential());
    assert_eq!(prefix.alternation_depth(), 1);
    assert_eq!(prefix.outermost_kind(), Some(QuantifierKind::Forall));
    assert_eq!(prefix.binders[0].kind, QuantifierKind::Forall);
    assert_eq!(prefix.binders[1].kind, QuantifierKind::Exists);
}

#[test]
fn test_quantifier_prefix_exists_forall() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let p_xy = Expr::app(Expr::app(p, Expr::bvar(1)), Expr::bvar(0));

    let inner_forall = Expr::pi(BinderInfo::Default, ty_b, p_xy);

    let exists_const = Expr::const_(Name::from_string("Exists"), vec![]);
    let outer_lam = Expr::lam(BinderInfo::Default, ty_a.clone(), inner_forall);
    let outer_exists = Expr::app(Expr::app(exists_const, ty_a), outer_lam);

    let prop = bridge.classify_prop(&outer_exists);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("exists-forall prefix should flatten");

    assert_eq!(prefix.len(), 2);
    assert!(!prefix.is_purely_universal());
    assert!(!prefix.is_purely_existential());
    assert_eq!(prefix.alternation_depth(), 1);
    assert_eq!(prefix.outermost_kind(), Some(QuantifierKind::Exists));
    assert_eq!(prefix.binders[0].kind, QuantifierKind::Exists);
    assert_eq!(prefix.binders[1].kind, QuantifierKind::Forall);
}

#[test]
fn test_quantifier_prefix_alternation_depth_2() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let ty_c = Expr::const_(Name::from_string("C"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let p_xyz = Expr::app(
        Expr::app(Expr::app(p, Expr::bvar(2)), Expr::bvar(1)),
        Expr::bvar(0),
    );

    let inner_forall = Expr::pi(BinderInfo::Default, ty_c, p_xyz);

    let exists_const = Expr::const_(Name::from_string("Exists"), vec![]);
    let middle_lam = Expr::lam(BinderInfo::Default, ty_b.clone(), inner_forall);
    let middle_exists = Expr::app(Expr::app(exists_const, ty_b), middle_lam);
    let outer_forall = Expr::pi(BinderInfo::Default, ty_a, middle_exists);

    let prop = bridge.classify_prop(&outer_forall);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("alternating prefix should flatten");

    assert_eq!(prefix.len(), 3);
    assert_eq!(prefix.alternation_depth(), 2);
    assert_eq!(prefix.binders[0].kind, QuantifierKind::Forall);
    assert_eq!(prefix.binders[1].kind, QuantifierKind::Exists);
    assert_eq!(prefix.binders[2].kind, QuantifierKind::Forall);
}

#[test]
fn test_skolem_dependencies_forall_exists() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let p_xy = Expr::app(Expr::app(p, Expr::bvar(1)), Expr::bvar(0));

    let exists_const = Expr::const_(Name::from_string("Exists"), vec![]);
    let inner_lam = Expr::lam(BinderInfo::Default, ty_b.clone(), p_xy);
    let inner_exists = Expr::app(Expr::app(exists_const, ty_b), inner_lam);
    let outer_forall = Expr::pi(BinderInfo::Default, ty_a, inner_exists);

    let prop = bridge.classify_prop(&outer_forall);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("forall-exists skolem dependencies should flatten");
    let deps = prefix.skolem_dependencies();

    let y_deps = deps.get(&0).expect("y should have dependencies");
    assert_eq!(y_deps.len(), 1);
    assert!(y_deps.contains(&1));
}

#[test]
fn test_skolem_dependencies_complex() {
    let env = Environment::new();
    let bridge = SmtBridge::new(&env);

    let ty_a = Expr::const_(Name::from_string("A"), vec![]);
    let ty_b = Expr::const_(Name::from_string("B"), vec![]);
    let ty_c = Expr::const_(Name::from_string("C"), vec![]);
    let ty_d = Expr::const_(Name::from_string("D"), vec![]);
    let p = Expr::const_(Name::from_string("P"), vec![]);
    let p_xyzw = Expr::app(
        Expr::app(
            Expr::app(Expr::app(p, Expr::bvar(3)), Expr::bvar(2)),
            Expr::bvar(1),
        ),
        Expr::bvar(0),
    );

    let exists_const = Expr::const_(Name::from_string("Exists"), vec![]);
    let lam_w = Expr::lam(BinderInfo::Default, ty_d.clone(), p_xyzw);
    let exists_w = Expr::app(Expr::app(exists_const.clone(), ty_d), lam_w);
    let forall_z = Expr::pi(BinderInfo::Default, ty_c, exists_w);
    let lam_y = Expr::lam(BinderInfo::Default, ty_b.clone(), forall_z);
    let exists_y = Expr::app(Expr::app(exists_const, ty_b), lam_y);
    let forall_x = Expr::pi(BinderInfo::Default, ty_a, exists_y);

    let prop = bridge.classify_prop(&forall_x);
    let prefix = bridge
        .flatten_quantifier_prefix(&prop)
        .expect("complex skolem dependencies should flatten");
    let deps = prefix.skolem_dependencies();

    let y_deps = deps.get(&2).expect("y should have dependencies");
    assert_eq!(y_deps.len(), 1);

    let w_deps = deps.get(&0).expect("w should have dependencies");
    assert_eq!(w_deps.len(), 2);
}

#[test]
fn test_add_hypothesis_with_prefix_analysis_simple() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let ty = Expr::const_(Name::from_string("A"), vec![]);
    let a = Expr::fvar(FVarId::new(1));
    let b = Expr::fvar(FVarId::new(2));
    let eq = make_eq(ty, a, b);

    let depth = bridge.add_hypothesis_with_prefix_analysis(&eq);
    assert_eq!(depth, Ok(0));
}

#[test]
fn test_add_hypothesis_with_prefix_analysis_mixed() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let outer_forall = make_mixed_quantifier_with_trigger();

    let depth = bridge.add_hypothesis_with_prefix_analysis(&outer_forall);
    assert_eq!(depth, Ok(1));
}

#[test]
fn test_mixed_prefix_analysis_marks_synthesized_origin() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);

    let depth = bridge.add_hypothesis_with_prefix_analysis(&make_mixed_quantifier_with_trigger());

    assert_eq!(depth, Ok(1));
    assert!(matches!(
        bridge.pending_foralls[0].origin.as_ref(),
        Some(QuantifierOrigin::Synthesized)
    ));
}

#[test]
fn test_mixed_prefix_analysis_preserves_named_origin() {
    use crate::premise::PremiseId;

    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let name = Name::from_string("mixed_origin_theorem");

    let depth = bridge.add_hypothesis_with_prefix_analysis_and_premise(
        &make_mixed_quantifier_with_trigger(),
        Some(PremiseOrigin::new(name.clone(), PremiseId(7))),
    );

    assert_eq!(depth, Ok(1));
    assert_eq!(
        bridge.pending_foralls[0]
            .origin
            .as_ref()
            .and_then(QuantifierOrigin::name),
        Some(&name)
    );
    assert_eq!(
        bridge.pending_foralls[0]
            .origin
            .as_ref()
            .and_then(QuantifierOrigin::premise_id),
        Some(PremiseId(7))
    );
}

#[test]
fn test_mixed_prefix_analysis_infers_local_origin_from_fvar() {
    let env = setup_env();
    let mut bridge = SmtBridge::new(&env);
    let fvar = FVarId::new(41);

    let depth = bridge.add_hypothesis_with_prefix_analysis_opts(
        &make_mixed_quantifier_with_trigger(),
        HypothesisOpts::new().with_fvar(fvar),
    );

    assert_eq!(depth, Ok(1));
    assert!(matches!(
        bridge.pending_foralls[0].origin.as_ref(),
        Some(QuantifierOrigin::Local { fvar_id }) if *fvar_id == fvar
    ));
}
