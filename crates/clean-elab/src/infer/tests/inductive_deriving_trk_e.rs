// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Track E — deriving completeness soundness tests.
//!
//! Covers two gaps the previous derive handlers got wrong:
//!  1. RECURSIVE/FIELDED inductive `BEq`: the casesOn minors now BIND each
//!     constructor's fields and compare them via `@BEq.beq`, so genuinely
//!     different values (e.g. `circle true` vs `circle false`) reduce to
//!     `Bool.false` — not the old tag-only / always-`Bool.true` bug.
//!  2. PARAMETRIC structure `Inhabited`/`BEq` (e.g. `Pair (α β : Type)`): the
//!     instance type/value telescopes now thread the type parameters and their
//!     class constraints with consistent de Bruijn indices and the correct
//!     per-class universe level, so the kernel accepts them.
//!
//! Each NEW kernel term is checked for soundness two ways:
//!  * `infer_type` succeeds when the instance is re-added to a fresh env that
//!    has ONLY the type registered (strict kernel type check), and
//!  * `env.axiom_deps(instance)` is EMPTY (no `sorry`/`sorryAx`/axioms leaked).

use super::*;

use clean_kernel::{ExprKind, TypeChecker};

fn expr_is_const(expr: &Expr, expected: &str) -> bool {
    matches!(expr.kind(), ExprKind::Const(name, _) if name.to_string() == expected)
}

/// Find a derived instance by class name in an `ElabResult`'s instance list.
fn find_instance<'a>(result: &'a ElabResult, class: &str) -> &'a crate::infer::DerivedInstance {
    let insts = match result {
        ElabResult::Inductive {
            derived_instances, ..
        } => derived_instances,
        ElabResult::Structure {
            derived_instances, ..
        } => derived_instances,
        other => panic!("expected Inductive/Structure, got {other:?}"),
    };
    insts
        .iter()
        .find(|i| i.class_name == Name::from_string(class))
        .unwrap_or_else(|| panic!("missing derived {class} instance"))
}

/// Re-add a derived instance to a FRESH env that has only `prelude_decls`
/// registered, exercising the strict kernel type check (infer_type) on the
/// committed term. Returns the populated env so axiom deps can be queried.
fn kernel_check_instance(
    inst: &crate::infer::DerivedInstance,
    prelude_decls: &[&str],
) -> Environment {
    let mut env = Environment::with_prelude();
    for src in prelude_decls {
        let decl = parse_decl_for_elab(src).expect("decl should parse");
        crate::elaborate_decl_and_register(&mut env, &decl)
            .expect("supporting decl should register");
    }
    let inst_decl = Declaration::Definition {
        name: inst.name.clone(),
        level_params: inst.level_params.clone(),
        type_: inst.ty.clone(),
        value: inst.val.clone(),
        is_reducible: true,
    };
    env.add_decl(inst_decl).unwrap_or_else(|e| {
        panic!(
            "instance {} must pass strict kernel check: {e:?}",
            inst.name
        )
    });
    env
}

/// Assert the registered instance has an EMPTY axiom-dependency closure.
fn assert_axiom_free(env: &Environment, name: &Name) {
    let deps = env
        .axiom_deps(name)
        .unwrap_or_else(|| panic!("axiom_deps should resolve for {name}"));
    assert!(
        deps.is_empty(),
        "derived instance {name} must be axiom-free (no sorry/sorryAx), got {:?}",
        deps.iter().map(|n| n.to_string()).collect::<Vec<_>>()
    );
}

/// Gap (1): fielded multi-ctor inductive `BEq` binds and compares fields, and
/// the derived term is kernel-sound + axiom-free, and reduces `circle true ==
/// circle false` to `Bool.false`.
#[test]
fn trk_e_beq_fielded_inductive_binds_and_distinguishes_fields() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(
        r"inductive Shape
| circle : Bool -> Shape
| rect : Bool -> Bool -> Shape
deriving BEq",
    )
    .unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("Shape deriving BEq should elaborate + register");

    let beq = find_instance(&result, "BEq");
    assert_eq!(beq.name, Name::from_string("instShapeBEq"));

    // The body must NOT be the degenerate always-true fallback: it has to
    // mention BEq.beq (the per-field comparison) and Bool.false (the
    // ctor-mismatch / field-mismatch arm).
    let beq_val = format!("{:?}", beq.val);
    assert!(
        beq_val.contains("beq") && beq_val.contains("false"),
        "fielded BEq must compare fields (BEq.beq) with a false arm, got {beq_val}"
    );
    assert!(
        !beq_val.contains("sorry") && !beq_val.contains("sorryAx"),
        "BEq instance must not contain sorry/sorryAx, got {beq_val}"
    );

    // Strict kernel check on a fresh env with only Shape registered.
    let env2 = kernel_check_instance(
        beq,
        &[r"inductive Shape
| circle : Bool -> Shape
| rect : Bool -> Bool -> Shape"],
    );
    // Soundness: axiom-free closure.
    assert_axiom_free(&env2, &beq.name);
    assert_axiom_free(&env, &beq.name);

    // Reduction: extract the beq function (last arg of BEq.mk … beq_func).
    let args = beq.val.get_app_args();
    let beq_func = args.last().copied().expect("BEq.mk should expose beq fn");

    let circle = Expr::const_(Name::from_string("Shape.circle"), vec![]);
    let btrue = Expr::const_(Name::from_string("Bool.true"), vec![]);
    let bfalse = Expr::const_(Name::from_string("Bool.false"), vec![]);
    let circle_t = Expr::app(circle.clone(), btrue.clone());
    let circle_f = Expr::app(circle, bfalse);

    let tc = TypeChecker::new(&env);
    // circle true == circle true ⇒ Bool.true
    let same = Expr::app(
        Expr::app(beq_func.clone(), circle_t.clone()),
        circle_t.clone(),
    );
    assert!(
        expr_is_const(&tc.whnf(&same), "Bool.true"),
        "circle true == circle true must reduce to Bool.true"
    );
    // circle true == circle false ⇒ Bool.false  (the field-binding payoff:
    // proves it is NOT the always-true bug).
    let diff = Expr::app(Expr::app(beq_func.clone(), circle_t), circle_f);
    assert!(
        expr_is_const(&tc.whnf(&diff), "Bool.false"),
        "circle true == circle false must reduce to Bool.false (field binding)"
    );
}

/// Regression: an all-nullary enum still distinguishes constructors (the field-
/// binding builder degenerates to a correct tag comparison).
#[test]
fn trk_e_beq_nullary_enum_still_distinguishes_tags() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(
        r"inductive Color
| red
| green
| blue
deriving BEq",
    )
    .unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl).unwrap();
    let beq = find_instance(&result, "BEq");

    let args = beq.val.get_app_args();
    let beq_func = args.last().copied().unwrap();
    let red = Expr::const_(Name::from_string("Color.red"), vec![]);
    let green = Expr::const_(Name::from_string("Color.green"), vec![]);
    let tc = TypeChecker::new(&env);
    let rr = Expr::app(Expr::app(beq_func.clone(), red.clone()), red.clone());
    let rg = Expr::app(Expr::app(beq_func.clone(), red), green);
    assert!(
        expr_is_const(&tc.whnf(&rr), "Bool.true"),
        "red == red ⇒ true"
    );
    assert!(
        expr_is_const(&tc.whnf(&rg), "Bool.false"),
        "red == green ⇒ false"
    );
    assert_axiom_free(&env, &beq.name);
}

/// Gap (2): parametric structure `Inhabited` + `BEq` register, pass the strict
/// kernel check, and are axiom-free.
#[test]
fn trk_e_parametric_pair_inhabited_and_beq_are_kernel_sound() {
    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(
        r"structure Pair (α : Type) (β : Type) where
  fst : α
  snd : β
deriving Inhabited, BEq",
    )
    .unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("parametric Pair deriving Inhabited, BEq should register");

    let pair_src = r"structure Pair (α : Type) (β : Type) where
  fst : α
  snd : β";

    for class in ["Inhabited", "BEq"] {
        let inst = find_instance(&result, class);
        let val = format!("{:?}", inst.val);
        assert!(
            !val.contains("sorry") && !val.contains("sorryAx"),
            "parametric {class} instance must be sorry-free, got {val}"
        );
        // Strict kernel check on a fresh env with only Pair registered.
        let env2 = kernel_check_instance(inst, &[pair_src]);
        assert_axiom_free(&env2, &inst.name);
        // And axiom-free in the original env too.
        assert_axiom_free(&env, &inst.name);
    }
}
