// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn expression(context: &mut ElabCtx<'_>, source: &str) -> Expr {
    context
        .elaborate(&clean_parser::parse_expr(source).expect("control parses"))
        .unwrap_or_else(|error| panic!("{source}: {error}"))
}

fn projection_scope(wrong_product: bool) {
    let env = Environment::with_prelude();
    let mut context = ElabCtx::new(&env);
    let nat_pair = expression(&mut context, "Nat × Nat");
    let a_ty = expression(
        &mut context,
        if wrong_product {
            "Nat × Bool"
        } else {
            "Nat × Nat"
        },
    );
    let a = context.push_local(SurfaceName::from_name(Name::from_string("a")), a_ty);
    let b = context.push_local(
        SurfaceName::from_name(Name::from_string("b")),
        nat_pair.clone(),
    );
    let expected = expression(&mut context, "a.1 = b.1");
    let scope: Vec<_> = context.locals.iter().cloned().collect();
    let left = context
        .metas
        .fresh_with_locals(nat_pair.clone(), scope.clone());
    let right = context.metas.fresh_with_locals(nat_pair, scope);
    let body = expected
        .abstract_fvar(a)
        .instantiate(&Expr::fvar(MetaState::to_fvar(left)))
        .abstract_fvar(b)
        .instantiate(&Expr::fvar(MetaState::to_fvar(right)));
    let function_type = Expr::pi(BinderInfo::Default, Expr::prop(), body);
    context.current_expected_type = Some(expected);
    let argument = SurfaceArg::positional(clean_parser::parse_expr("0").expect("argument parses"));
    let armed = context.propagate_expected_type(&function_type, &[argument]);
    for id in [left, right] {
        if let Some(meta) = context.metas.get(id) {
            if let Some(value) = &meta.assignment {
                eprintln!(
                    "candidate {id:?}: declared={}, value={}, inferred={:?}",
                    meta.ty,
                    value,
                    context.infer_type_full(value)
                );
            }
        }
    }
    assert_eq!(armed, wrong_product, "only a typed propagation may disarm");
    assert_eq!(context.metas.is_assigned(left), !wrong_product);
    assert_eq!(context.metas.is_assigned(right), !wrong_product);
    assert_eq!(context.metas.scope_depth(), 0, "scope must close exactly");
}

#[test]
fn expected_result_assignment_rolls_back_wrong_record_type() {
    projection_scope(true);
}

#[test]
fn expected_result_assignment_retains_well_typed_record_solutions() {
    projection_scope(false);
}

fn checked(env: &mut Environment, source: &str) -> Result<(), ElabError> {
    for declaration in clean_parser::parse_file(source).expect("source control parses") {
        let result = crate::elaborate_decl_and_register(env, &declaration)?;
        let mut leaves = Vec::new();
        result.leaf_decls(&mut leaves);
        for leaf in leaves {
            if let ElabResult::Failed { error, .. } = leaf {
                return Err((**error).clone());
            }
        }
    }
    Ok(())
}

#[test]
fn expected_result_assignment_project_source_has_checked_empty_closure() {
    let mut env = Environment::with_prelude();
    checked(
        &mut env,
        include_str!("../../../../tests/fixtures/expected_result_assignment_typing/project.lean"),
    )
    .expect("projected congrArg must wait for the real equality endpoints");
    assert_checked_empty_closure(&env, "project");
}

fn assert_checked_empty_closure(env: &Environment, name: &str) {
    let name = Name::from_string(name);
    let info = env.get_const(&name).expect("real theorem registers");
    TypeChecker::new(env)
        .check_type(info.value.as_ref().expect("proof body"), &info.type_)
        .expect("registered proof rechecks in the kernel");
    assert!(env.axiom_deps(&name).expect("axiom closure").is_empty());
    assert!(env
        .trust_marker_deps(&name)
        .expect("trust closure")
        .is_empty());
}

#[test]
fn expected_result_assignment_codata_seed_proof_has_checked_empty_closure() {
    let mut env = Environment::with_prelude();
    crate::codata_seed::ensure_codata_seeds(&mut env)
        .expect("the byte-identical real codata seed elaborates");
    assert_checked_empty_closure(&env, "Codata.ilabel_step");
}

#[test]
fn expected_result_assignment_eta_sources_use_kernel_definitional_equality() {
    let mut env = Environment::with_prelude();
    for (name, source) in [
        ("unitEta", include_str!("../../../../tests/fixtures/expected_result_assignment_typing/unit_eta.lean")),
        ("subtypeEtaApply", include_str!("../../../../tests/fixtures/expected_result_assignment_typing/subtype_eta_apply.lean")),
    ] {
        checked(&mut env, source).unwrap_or_else(|error| panic!("{name}: {error}"));
        assert_checked_empty_closure(&env, name);
    }
}

#[test]
fn expected_result_assignment_kernel_eta_witnesses_check() {
    let env = Environment::with_prelude();
    for subtype in [false, true] {
        let mut context = ElabCtx::new(&env);
        let goal = if subtype {
            for (name, source) in [("p", "Nat → Prop"), ("f", "Nat → Subtype p"), ("i", "Nat")]
            {
                let ty = expression(&mut context, source);
                context.push_local(SurfaceName::from_name(Name::from_string(name)), ty);
            }
            expression(
                &mut context,
                "@Subtype.mk Nat p (f i).val (f i).property = f i",
            )
        } else {
            let ty = expression(&mut context, "PUnit.{1}");
            context.push_local(SurfaceName::from_name(Name::from_string("x")), ty.clone());
            context.push_local(SurfaceName::from_name(Name::from_string("y")), ty);
            expression(&mut context, "x = y")
        };
        let goal = context
            .metas
            .instantiate_levels(&context.metas.instantiate(&goal));
        let ExprKind::Const(head, levels) = goal.get_app_fn().kind() else {
            panic!("equality goal");
        };
        assert_eq!(*head, Name::from_string("Eq"));
        let args = goal.get_app_args();
        let proof = Expr::apps(
            Expr::const_(Name::from_string("Eq.refl"), levels.clone()),
            [args[0].clone(), args[1].clone()],
        );
        TypeChecker::with_context(&env, context.demand_local_ctx(&[&proof, &goal]))
            .check_type(&proof, &goal)
            .expect("the same eta equality has a fully checked core reflexivity witness");
    }
}

#[test]
fn expected_result_assignment_eta_refusals_preserve_fields_and_transparency() {
    let mut env = Environment::with_prelude();
    for (name, source) in [
        (
            "unitBad",
            include_str!(
                "../../../../tests/fixtures/expected_result_assignment_typing/unit_bad.lean"
            ),
        ),
        (
            "subtypeBad",
            include_str!(
                "../../../../tests/fixtures/expected_result_assignment_typing/subtype_bad.lean"
            ),
        ),
    ] {
        checked(&mut env, source).expect_err("distinct fields are not eta equal");
        assert!(env.get_const(&Name::from_string(name)).is_none());
    }
    let source = include_str!(
        "../../../../tests/fixtures/expected_result_assignment_typing/irreducible_bad.lean"
    );
    let declarations = clean_parser::parse_file(source).expect("irreducible control parses");
    crate::elaborate_decl_and_register(&mut env, &declarations[0]).expect("definition checks");
    assert!(env.get_const(&Name::from_string("hiddenNat")).is_some());
    let error = checked(&mut env, "theorem hiddenBad : hiddenNat = 0 := rfl")
        .expect_err("irreducible unfolding cannot justify elaboration");
    assert!(error.to_string().contains("Type mismatch"), "{error}");
    assert!(env.get_const(&Name::from_string("hiddenBad")).is_none());
}

#[test]
fn expected_result_assignment_source_refusals_follow_valid_setup() {
    let mut env = Environment::with_prelude();
    checked(
        &mut env,
        "theorem setup (a : Nat × Bool) (b : Nat × Nat) (h : (a.1, (0 : Nat)) = b) : (a.1, (0 : Nat)) = b := h",
    )
    .expect("the same local product/equality telescope checks");
    for (name, source) in [
        (
            "projectSame",
            include_str!("../../../../tests/fixtures/expected_result_assignment_typing/project_same_type.lean"),
        ),
        (
            "projectBadGoal",
            include_str!("../../../../tests/fixtures/expected_result_assignment_typing/project_false_goal.lean"),
        ),
        (
            "projectBadProof",
            include_str!("../../../../tests/fixtures/expected_result_assignment_typing/project_wrong_projection.lean"),
        ),
    ] {
        let before = env.constants().count();
        let error = checked(&mut env, source).expect_err("Lean-refused source must refuse");
        assert!(error.to_string().contains("Type mismatch"), "{error}");
        assert_eq!(env.constants().count(), before);
        assert!(env.get_const(&Name::from_string(name)).is_none());
    }
}
