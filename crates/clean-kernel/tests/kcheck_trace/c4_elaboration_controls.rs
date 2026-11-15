// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{nat_environment, BinderData, Expr, Level, Name};

#[test]
fn nested_constructor_universes_come_from_the_major_domain_not_parameter_names() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType, RecursorArgOrder};
    use clean_kernel::kcheck_trace::core::CoreTracer;
    use clean_kernel::tc::TypeChecker;
    let mut env = nat_environment();
    let u = Name::from_string("c4_u");
    let v = Name::from_string("c4_v");
    let lu = Level::param(u.clone());
    let lv = Level::param(v.clone());
    let max = Level::max(lu.clone(), lv.clone());
    let pi = |d, b| Expr::pi(BinderData::default(), d, b);
    let sort_u = Expr::sort(Level::succ(lu.clone()));
    let sort_v = Expr::sort(Level::succ(lv.clone()));
    let result_sort = Expr::sort(Level::succ(max.clone()));
    let prod = Name::from_string("Prod");
    let prod_mk = Name::from_string("Prod.mk");
    let prod_type = pi(sort_u.clone(), pi(sort_v.clone(), result_sort.clone()));
    let prod_ctor = pi(
        sort_u.clone(),
        pi(
            sort_v.clone(),
            pi(
                Expr::bvar(1),
                pi(
                    Expr::bvar(1),
                    Expr::apps(
                        Expr::const_(prod.clone(), vec![lu.clone(), lv.clone()]),
                        [Expr::bvar(3), Expr::bvar(2)],
                    ),
                ),
            ),
        ),
    );
    env.add_inductive_core(InductiveDecl {
        level_params: vec![u.clone(), v.clone()],
        num_params: 2,
        types: vec![InductiveType {
            name: prod.clone(),
            type_: prod_type,
            constructors: vec![Constructor {
                name: prod_mk.clone(),
                type_: prod_ctor,
            }],
        }],
    })
    .expect("polymorphic product");
    let tree = Name::from_string("C4NestedTree");
    let leaf = Name::from_string("C4NestedTree.leaf");
    let node = Name::from_string("C4NestedTree.node");
    let tree_at = |a, b| {
        Expr::apps(
            Expr::const_(tree.clone(), vec![lu.clone(), lv.clone()]),
            [a, b],
        )
    };
    let leaf_type = pi(
        sort_u.clone(),
        pi(
            sort_v.clone(),
            pi(Expr::bvar(1), tree_at(Expr::bvar(2), Expr::bvar(1))),
        ),
    );
    // Prod uses levels (v,max u v), deliberately different from the root's
    // (u,v) despite sharing the same universe parameter NAMES.
    let field = Expr::apps(
        Expr::const_(prod.clone(), vec![lv.clone(), max]),
        [Expr::bvar(0), tree_at(Expr::bvar(1), Expr::bvar(0))],
    );
    let node_type = pi(
        sort_u.clone(),
        pi(
            sort_v.clone(),
            pi(field, tree_at(Expr::bvar(2), Expr::bvar(1))),
        ),
    );
    env.add_inductive_core(InductiveDecl {
        level_params: vec![u.clone(), v.clone()],
        num_params: 2,
        types: vec![InductiveType {
            name: tree.clone(),
            type_: pi(sort_u, pi(sort_v, result_sort)),
            constructors: vec![
                Constructor {
                    name: leaf.clone(),
                    type_: leaf_type,
                },
                Constructor {
                    name: node,
                    type_: node_type,
                },
            ],
        }],
    })
    .expect("nested tree");
    let rec = env
        .recursors()
        .find(|r| r.inductive_name == tree && r.major_induct() == Some(&prod))
        .cloned()
        .expect("nested product auxiliary recursor");
    assert_eq!(rec.arg_order, RecursorArgOrder::MajorAfterMinors);
    assert_eq!(rec.num_params, 2);
    assert_eq!(rec.num_indices, 0);
    let one = Level::succ(Level::zero());
    let levels: Vec<_> = rec
        .level_params
        .iter()
        .map(|p| if p == &u { Level::zero() } else { one.clone() })
        .collect();
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let type_zero = Expr::type_();
    let tree_instance = Expr::apps(
        Expr::const_(tree, vec![Level::zero(), one.clone()]),
        [nat.clone(), type_zero.clone()],
    );
    let leaf_value = Expr::apps(
        Expr::const_(leaf, vec![Level::zero(), one.clone()]),
        [nat.clone(), type_zero.clone(), zero.clone()],
    );
    let major = Expr::apps(
        Expr::const_(prod_mk, vec![one.clone(), one]),
        [type_zero.clone(), tree_instance, nat.clone(), leaf_value],
    );
    let checker = TypeChecker::new(&env);
    fn constant_lambda(ty: &Expr, value: &Expr, checker: &TypeChecker<'_>) -> Expr {
        let ty = checker.whnf(ty);
        if let clean_kernel::expr::ExprKind::Pi(b, d, body) = ty.kind() {
            Expr::lam(
                *b,
                d.as_ref().clone(),
                constant_lambda(body, value, checker),
            )
        } else {
            value.clone()
        }
    }
    let pm = (rec.num_params + rec.num_motives) as usize;
    let major_index = pm + rec.num_minors as usize;
    let mut ty = rec
        .type_
        .instantiate_level_params_direct(&rec.level_params, &levels);
    let mut raw = Expr::const_(rec.name, levels);
    for position in 0..=major_index {
        let telescope = checker.whnf(&ty);
        let clean_kernel::expr::ExprKind::Pi(_, domain, body) = telescope.kind() else {
            panic!("recursor telescope")
        };
        let arg = if position == 0 {
            nat.clone()
        } else if position == 1 {
            type_zero.clone()
        } else if position < pm {
            constant_lambda(domain, &nat, &checker)
        } else if position < major_index {
            constant_lambda(domain, &zero, &checker)
        } else {
            major.clone()
        };
        ty = body.instantiate(&arg);
        raw = Expr::app(raw, arg);
    }
    let inferred = checker
        .infer_type(&raw)
        .expect("typed auxiliary application");
    assert!(checker.is_def_eq(&inferred, &nat));
    assert!(checker.is_def_eq(&raw, &zero));
    let mut tracer = CoreTracer::new(&env, 1000000);
    let (term, _) = tracer.check(&raw).expect("annotated auxiliary application");
    let result = tracer
        .whnf(&term)
        .expect("nested iota with actual major universes");
    assert!(checker.is_def_eq(&result.erase(), &zero));
    assert!(
        tracer
            .constructor_levels
            .get("identical")
            .copied()
            .unwrap_or(0)
            > 0
    );
    assert!(!tracer.constructor_levels.contains_key("failed"));
    assert!(!tracer
        .constructor_levels
        .contains_key("major_domain_head_unavailable"));
    assert!(tracer.spine_comparisons.iter().any(|e| e.family == "Prod"));
}

#[test]
fn projection_congruence_and_structure_eta_do_not_cycle_in_conversion_search() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};
    use clean_kernel::kcheck_trace::core::{CoreTracer, Refusal};
    use clean_kernel::tc::TypeChecker;
    let mut env = clean_kernel::env::Environment::default();
    let name = Name::from_string("TraceTypeBox");
    let ty = Expr::const_(name.clone(), vec![]);
    env.add_inductive_core(InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: name.clone(),
            type_: Expr::sort(Level::succ(Level::succ(Level::zero()))),
            constructors: vec![Constructor {
                name: Name::from_string("TraceTypeBox.mk"),
                type_: Expr::pi(BinderData::default(), Expr::type_(), ty.clone()),
            }],
        }],
    })
    .expect("type-valued structure");
    let field = |i| Expr::proj(name.clone(), 0, Expr::bvar(i));
    // fun x y : Box => fun f : x.field -> x.field => fun a : y.field => f a
    // Distinct neutral projections cannot convert. Comparing their receivers
    // through congruence and then eta-expanding the receivers must not loop.
    let bad = Expr::lam(
        BinderData::default(),
        ty.clone(),
        Expr::lam(
            BinderData::default(),
            ty,
            Expr::lam(
                BinderData::default(),
                Expr::pi(BinderData::default(), field(1), field(2)),
                Expr::lam(
                    BinderData::default(),
                    field(1),
                    Expr::app(Expr::bvar(1), Expr::bvar(0)),
                ),
            ),
        ),
    );
    let checker = TypeChecker::new(&env);
    assert!(checker.infer_type_full(&bad).is_err());
    assert!(!checker.heartbeat_spent());
    let mut tracer = CoreTracer::new(&env, 10000);
    assert!(matches!(tracer.check(&bad), Err(Refusal::Check(_))));
    assert!(tracer.conversion_cycles_cut > 0);
    let previous = tracer.conversion_cycles_cut;
    assert!(matches!(tracer.check(&bad), Err(Refusal::Check(_))));
    assert!(
        tracer.conversion_cycles_cut > previous,
        "a later check must search again rather than inherit an equality answer"
    );
}
