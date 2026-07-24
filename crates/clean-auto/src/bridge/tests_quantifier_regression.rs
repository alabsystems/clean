// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Quantifier instantiation regression tests for flattened nested binders.

use super::*;
use clean_kernel::env::Declaration;

fn setup_binary_relation_env() -> Environment {
    let mut env = Environment::new();

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("A"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("A should be declared");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("B"),
        level_params: vec![],
        type_: Expr::type_(),
    })
    .expect("B should be declared");
    env.add_decl(Declaration::Axiom {
        name: Name::from_string("Rel"),
        level_params: vec![],
        type_: Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("A"), vec![]),
            Expr::pi(
                BinderInfo::Default,
                Expr::const_(Name::from_string("B"), vec![]),
                Expr::prop(),
            ),
        ),
    })
    .expect("Rel should be declared");

    env
}

fn make_exists(ty: Expr, body: Expr) -> Expr {
    Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Exists"), vec![]),
            ty.clone(),
        ),
        Expr::lam(BinderInfo::Default, ty, body),
    )
}

fn make_rel(lhs: Expr, rhs: Expr) -> Expr {
    Expr::app(
        Expr::app(Expr::const_(Name::from_string("Rel"), vec![]), lhs),
        rhs,
    )
}

fn find_named_term_expr(bridge: &SmtBridge<'_>, expected_name: &str) -> Expr {
    let term_id = (0..bridge.stats().num_terms)
        .find_map(|idx| match bridge.smt.get_term(TermId(idx as u32)) {
            Some(crate::smt::SmtTerm::Const(sym)) if sym.name() == expected_name => {
                Some(TermId(idx as u32))
            }
            _ => None,
        })
        .unwrap_or_else(|| panic!("missing SMT constant '{expected_name}'"));

    bridge
        .term_to_expr
        .get(&term_id)
        .cloned()
        .unwrap_or_else(|| panic!("missing Expr mapping for SMT constant '{expected_name}'"))
}

fn assert_rel_atom_present(
    bridge: &SmtBridge<'_>,
    outer_name: &str,
    inner_name: &str,
    context: &str,
) {
    let outer = find_named_term_expr(bridge, outer_name);
    let inner = find_named_term_expr(bridge, inner_name);
    let expected = make_rel(outer.clone(), inner.clone());
    let reversed = make_rel(inner, outer);

    let expected_key = ExprKey::from_expr(&expected).expect("expected atom should hash");
    let reversed_key = ExprKey::from_expr(&reversed).expect("reversed atom should hash");

    assert!(
        bridge.atom_to_var.contains_key(&expected_key),
        "{context}: expected instantiated atom should preserve declaration order"
    );
    assert!(
        !bridge.atom_to_var.contains_key(&reversed_key),
        "{context}: instantiated atom must not swap outer and inner binders"
    );
}

#[test]
fn test_nested_forall_hypothesis_instantiates_outer_then_inner_binders() {
    let env = setup_binary_relation_env();
    let mut bridge = SmtBridge::new(&env);

    let forall_expr = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("A"), vec![]),
        Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("B"), vec![]),
            make_rel(Expr::bvar(1), Expr::bvar(0)),
        ),
    );

    bridge
        .add_hypothesis(&forall_expr)
        .expect("nested forall should add successfully");

    assert_rel_atom_present(
        &bridge,
        "forall_witness_0_0",
        "forall_witness_1_1",
        "forall hypothesis fallback",
    );
}

#[test]
fn test_nested_exists_hypothesis_instantiates_outer_then_inner_binders() {
    let env = setup_binary_relation_env();
    let mut bridge = SmtBridge::new(&env);

    let exists_expr = make_exists(
        Expr::const_(Name::from_string("A"), vec![]),
        make_exists(
            Expr::const_(Name::from_string("B"), vec![]),
            make_rel(Expr::bvar(1), Expr::bvar(0)),
        ),
    );

    bridge
        .add_hypothesis(&exists_expr)
        .expect("nested exists should add successfully");

    assert_rel_atom_present(
        &bridge,
        "exists_witness_0_0",
        "exists_witness_1_1",
        "exists hypothesis fallback",
    );
}

#[test]
fn test_negated_nested_forall_instantiates_outer_then_inner_binders() {
    let env = setup_binary_relation_env();
    let mut bridge = SmtBridge::new(&env);

    let forall_expr = Expr::pi(
        BinderInfo::Default,
        Expr::const_(Name::from_string("A"), vec![]),
        Expr::pi(
            BinderInfo::Default,
            Expr::const_(Name::from_string("B"), vec![]),
            make_rel(Expr::bvar(1), Expr::bvar(0)),
        ),
    );

    let goal_class = bridge.classify_prop(&forall_expr);
    bridge
        .translate_negated_classified(&goal_class)
        .expect("negated nested forall should translate");

    assert_rel_atom_present(&bridge, "sk_0_0", "sk_1_1", "negated forall translation");
}

#[test]
fn test_negated_nested_exists_instantiates_outer_then_inner_binders() {
    let env = setup_binary_relation_env();
    let mut bridge = SmtBridge::new(&env);

    let exists_expr = make_exists(
        Expr::const_(Name::from_string("A"), vec![]),
        make_exists(
            Expr::const_(Name::from_string("B"), vec![]),
            make_rel(Expr::bvar(1), Expr::bvar(0)),
        ),
    );

    let goal_class = bridge.classify_prop(&exists_expr);
    bridge
        .translate_negated_classified(&goal_class)
        .expect("negated nested exists should translate");

    assert_rel_atom_present(
        &bridge,
        "neg_exists_witness_0_0",
        "neg_exists_witness_1_1",
        "negated exists translation",
    );
}
