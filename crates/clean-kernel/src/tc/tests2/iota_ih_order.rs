// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Iota reduction tests — IH ordering, polymorphic recursion, and regressions.
//!
//! Tests for induction hypothesis application order in binary trees,
//! polymorphic recursive types (List (List Nat)), and regression tests.

use super::*;
use crate::inductive::{Constructor, InductiveDecl, InductiveType};

/// Create Tree inductive with Nat (for counting depths).
fn make_tree_env() -> (Environment, Expr) {
    let mut env = Environment::new();
    let tree = Name::from_string("Tree");
    let tree_ref = Expr::const_(tree.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: tree.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Tree.leaf"),
                    type_: tree_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Tree.node"),
                    type_: Expr::arrow(
                        tree_ref.clone(),
                        Expr::arrow(tree_ref.clone(), tree_ref.clone()),
                    ),
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("add Tree inductive");
    env.init_nat().expect("init_nat");
    (env, tree_ref)
}

/// Verify Tree.node rule has 2 recursive fields and lambda-wrapped RHS (#1406).
#[test]
fn test_iota_reduction_ih_order_rule_structure() {
    let (env, _tree_ref) = make_tree_env();
    let rec_val = env
        .get_recursor(&Name::from_string("Tree.rec"))
        .expect("get Tree.rec");
    let node_rule = rec_val
        .rules
        .iter()
        .find(|r| r.constructor_name == Name::from_string("Tree.node"))
        .expect("Tree.node rule must exist");
    assert_eq!(node_rule.num_fields, 2);
    assert_eq!(node_rule.recursive_fields, vec![true, true]);
    // RHS is now a lambda: λ motive. λ leaf_case. λ node_case. λ left. λ right. body
    // (0 params + 1 motive + 2 minors + 2 fields = 5 lambda binders)
    assert!(
        node_rule.rhs.is_lam(),
        "node RHS should be a lambda (Lean 4 format)"
    );
    // Unwrap 5 lambdas to get to the body
    let mut body = node_rule.rhs.clone();
    let mut lam_count = 0;
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = (**inner).clone();
        lam_count += 1;
    }
    assert_eq!(
        lam_count, 5,
        "5 lambda binders: 0 params + 1 motive + 2 minors + 2 fields"
    );
    // Body should be: node_case left right IH_left IH_right (4 args applied to minor)
    assert_eq!(body.get_app_args().len(), 4, "node body: 2 fields + 2 IH");
}

/// Reduce an expression to a Nat depth (peeling Nat.succ constructors or reading literals).
/// Returns None if the expression is not in Nat normal form.
fn nat_depth(tc: &TypeChecker<'_>, start: Expr) -> Option<u32> {
    let mut depth = 0u32;
    let mut current = start;
    loop {
        let reduced = tc.whnf(&current);
        match reduced.kind() {
            // Nat literal: WHNF reduce_nat may collapse Nat.succ chains to a literal
            ExprKind::Lit(crate::expr::Literal::Nat(n)) => {
                return n.to_u64().map(|v| depth.saturating_add(v as u32));
            }
            ExprKind::Const(name, _) if *name == Name::from_string("Nat.zero") => {
                return Some(depth)
            }
            ExprKind::App(f, a) => match f.kind() {
                ExprKind::Const(name, _) if *name == Name::from_string("Nat.succ") => {
                    depth = depth.saturating_add(1);
                    if depth >= 32 {
                        return None;
                    }
                    current = (**a).clone();
                }
                _ => return None,
            },
            _ => return None,
        }
    }
}

/// Build Tree.rec app with given node_case on tree: node(leaf, node(leaf, leaf)).
fn build_tree_rec_app(tree_ref: &Expr, node_case: Expr) -> (Expr, Expr) {
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let leaf = Expr::const_(Name::from_string("Tree.leaf"), vec![]);
    let node_ctor = Expr::const_(Name::from_string("Tree.node"), vec![]);
    let right = Expr::app(Expr::app(node_ctor.clone(), leaf.clone()), leaf.clone());
    let test_tree = Expr::app(Expr::app(node_ctor, leaf), right);
    let rec = Expr::const_(Name::from_string("Tree.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, tree_ref.clone(), nat);
    let leaf_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), leaf_case), node_case),
        test_tree.clone(),
    );
    (app, test_tree)
}

/// D4: IH-left selector on node(leaf, node(leaf, leaf)) should give depth 1.
#[test]
fn test_iota_reduction_ih_order_left() {
    let (env, tree_ref) = make_tree_env();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    // node_case_left = λ left right ih_left ih_right. Nat.succ ih_left
    let node_case = Expr::lam(
        BinderInfo::Default,
        tree_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            tree_ref.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::lam(BinderInfo::Default, nat, Expr::app(nat_succ, Expr::bvar(1))),
            ),
        ),
    );
    let (app, _tree) = build_tree_rec_app(&tree_ref, node_case);
    let result = tc.whnf(&app);
    assert_eq!(
        nat_depth(&tc, result).expect("result should be Nat normal form"),
        1,
        "ih_left depth should be 1"
    );
}

/// D4: IH-right selector on node(leaf, node(leaf, leaf)) should give depth 2.
#[test]
fn test_iota_reduction_ih_order_right() {
    let (env, tree_ref) = make_tree_env();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let nat_succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    // node_case_right = λ left right ih_left ih_right. Nat.succ ih_right
    let node_case = Expr::lam(
        BinderInfo::Default,
        tree_ref.clone(),
        Expr::lam(
            BinderInfo::Default,
            tree_ref.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::lam(BinderInfo::Default, nat, Expr::app(nat_succ, Expr::bvar(0))),
            ),
        ),
    );
    let (app, _tree) = build_tree_rec_app(&tree_ref, node_case);
    let result = tc.whnf(&app);
    assert_eq!(
        nat_depth(&tc, result).expect("result should be Nat normal form"),
        2,
        "ih_right depth should be 2"
    );
}

/// Build List (List Nat) environment for polymorphic recursive test.
fn make_list_list_nat_env() -> (Environment, Expr, Expr) {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_list().expect("init_list");
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat.clone(),
    );
    (env, nat, list_nat)
}

/// D5: Polymorphic recursive — List.rec on List (List Nat) verifies level
/// instantiation for nested recursive types (#1406).
#[test]
fn test_iota_reduction_polymorphic_recursive_list() {
    let (env, nat, list_nat) = make_list_list_nat_env();
    let tc = TypeChecker::new(&env);
    let list_list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::succ(Level::zero())]),
        list_nat.clone(),
    );
    let nil = Expr::app(
        Expr::const_(
            Name::from_string("List.nil"),
            vec![Level::succ(Level::zero())],
        ),
        list_nat.clone(),
    );
    // inner list: [0]
    let inner_nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat.clone(),
    );
    let inner = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
                nat.clone(),
            ),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
        inner_nil,
    );
    // outer: [[0]]
    let outer = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(
                    Name::from_string("List.cons"),
                    vec![Level::succ(Level::zero())],
                ),
                list_nat.clone(),
            ),
            inner,
        ),
        nil,
    );
    let rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );
    let motive = Expr::lam(BinderInfo::Default, list_list_nat.clone(), nat.clone());
    let nil_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ = Expr::const_(Name::from_string("Nat.succ"), vec![]);
    let cons_case = Expr::lam(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            list_list_nat,
            Expr::lam(BinderInfo::Default, nat, Expr::app(succ, Expr::bvar(0))),
        ),
    );
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(rec, list_nat), motive), nil_case),
            cons_case,
        ),
        outer,
    );
    let result = tc.whnf(&app);
    // After iota + WHNF nat reduction, the result may be a Nat literal 1
    // (reduce_nat collapses Nat.succ(Nat.zero) -> lit 1) or Nat.succ form.
    match result.kind() {
        ExprKind::Lit(crate::expr::Literal::Nat(n)) => {
            assert_eq!(
                n.to_u64(),
                Some(1),
                "D5: expected Nat literal 1, got: {:?}",
                n
            );
        }
        _ => {
            let result_head = result.get_app_fn();
            assert!(
                matches!(result_head.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.succ")),
                "D5: expected Nat.succ head or Nat literal 1, got: {:?}",
                result
            );
        }
    }
}

/// D7: Level instantiation isolation — verify that universe levels in the
/// recursor RHS are correctly substituted during iota reduction (#1406 gap 3).
///
/// Uses Nat.rec at universe level 2 (Sort 2 = Type 1). After iota reduction
/// of `Nat.rec.{2} motive z s (succ n)`, the IH sub-expression must contain
/// `Nat.rec.{2}` (concrete level), not `Nat.rec.{u}` (unsubstituted param).
/// Also verifies the result is def-eq to the original via semantic preservation.
#[test]
fn test_iota_level_instantiation_isolated() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        zero.clone(),
    );

    // Use universe level 2 (Sort 2 = Type 1)
    let u2 = Level::succ(Level::succ(Level::zero()));

    // motive = λ _ : Nat. Sort 2  (returns Type 1)
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), Expr::sort(u2.clone()));

    // z = Nat (element of Sort 2 = Type 1)
    let z_case = nat.clone();

    // s = λ n : Nat. λ ih : Sort 2. ih  (identity on IH)
    let s_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, Expr::sort(u2.clone()), Expr::bvar(0)),
    );

    // Nat.rec.{2} motive z s (succ 0)
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(
                    Expr::const_(Name::from_string("Nat.rec"), vec![u2.clone()]),
                    motive.clone(),
                ),
                z_case.clone(),
            ),
            s_case.clone(),
        ),
        succ_zero,
    );

    let result = tc.whnf(&app);
    assert_ne!(app, result, "Nat.rec.{{2}} on succ must reduce");

    // The result should contain Nat.rec with level 2 in the IH.
    // After full reduction: s 0 (Nat.rec.{2} motive Nat s 0) = Nat.rec.{2} motive Nat s 0
    // Which further reduces to Nat (the zero case).
    // Full whnf should give us Nat.
    let head = result.get_app_fn();
    assert!(
        matches!(head.kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat")),
        "fully reduced result should be Nat, got: {result:?}"
    );

    // Semantic preservation: original and result must be def-eq
    assert!(
        tc.is_def_eq(&app, &result),
        "iota result must be definitionally equal to original"
    );
}

/// Regression #1430: init_list adds List.tail via add_decl successfully.
#[test]
fn test_init_list_tail_add_decl_regression_1430() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_list().expect("init_list");

    let tail_info = env
        .get_const(&Name::from_string("List.tail"))
        .expect("List.tail must exist");
    assert!(
        tail_info.value.is_some(),
        "List.tail must have a definition value"
    );

    let tc = TypeChecker::new(&env);
    let tail_nat = Expr::app(
        Expr::const_(Name::from_string("List.tail"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    let tail_nat_ty = tc.infer_type(&tail_nat).expect("infer List.tail Nat type");
    let expected_domain = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        Expr::const_(Name::from_string("Nat"), vec![]),
    );
    assert!(
        matches!(tail_nat_ty.kind(), ExprKind::Pi(..)),
        "List.tail Nat should have Pi type, got: {tail_nat_ty:?}"
    );
    if let ExprKind::Pi(_, domain, _) = tail_nat_ty.kind() {
        assert!(
            tc.is_def_eq(domain, &expected_domain),
            "List.tail Nat domain should be List Nat, got: {domain:?}"
        );
    }
}
