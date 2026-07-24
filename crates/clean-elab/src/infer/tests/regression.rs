// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Regression tests for elaboration edge cases

use super::*;

/// Issue #362: Regression test for recursor motive beta reduction in app elaboration
///
/// When elaborating applications with dependent function types, the expected argument type
/// may be an application of a motive function that needs to beta-reduce before unification.
/// For example, if we have:
///   `f : (n : Nat) → (motive n) → Result`
/// where `motive` is a lambda, then when we apply `f zero val`, the expected type for `val`
/// is `motive zero` which needs WHNF to become a concrete type before unification.
///
/// Fix: commits 0812fb6 and d09a518 added `expected_arg_ty = self.whnf(&expected_arg_ty)`
/// in application elaboration.
#[test]
fn test_issue362_motive_beta_reduction_in_app_elaboration() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();

    // Define MyBool inductive type with two constructors
    let mybool = Name::from_string("MyBool");
    let mybool_ref = Expr::const_(mybool.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: mybool.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyBool.false"),
                    type_: mybool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("MyBool.true"),
                    type_: mybool_ref.clone(),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();

    // Define MyNat inductive type (we can't rely on Nat being in Environment::new())
    let mynat = Name::from_string("MyNat");
    let mynat_ref = Expr::const_(mynat.clone(), vec![]);

    let nat_decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: mynat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyNat.zero"),
                    type_: mynat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("MyNat.succ"),
                    type_: Expr::arrow(mynat_ref.clone(), mynat_ref.clone()),
                },
            ],
        }],
    };
    env.add_inductive(nat_decl).unwrap();

    // Add a dependent function that takes a motive and a value at (motive MyBool.false)
    // dep_apply : (motive : MyBool → Type) → motive MyBool.false → Prop
    //
    // The key is that when we apply dep_apply to a concrete motive lambda,
    // the expected type for the second argument is `(motive MyBool.false)`
    // which needs beta-reduction to become the actual expected type.
    let dep_apply_type = Expr::pi(
        BinderInfo::Default,
        // motive : MyBool → Type
        Expr::pi(BinderInfo::Default, mybool_ref.clone(), Expr::type_()),
        Expr::pi(
            BinderInfo::Default,
            // motive MyBool.false (the application that needs WHNF)
            Expr::app(
                Expr::bvar(0), // motive
                Expr::const_(Name::from_string("MyBool.false"), vec![]),
            ),
            Expr::prop(),
        ),
    );

    env.add_decl(Declaration::Axiom {
        name: Name::from_string("dep_apply"),
        level_params: vec![],
        type_: dep_apply_type,
    })
    .unwrap();

    // Now try to elaborate: dep_apply (fun _ => MyNat) MyNat.zero
    // The motive is `fun _ => MyNat`, so `(motive MyBool.false)` beta-reduces to `MyNat`
    // Without WHNF, we'd try to unify `App motive MyBool.false` with `MyNat`, which would fail
    let mut ctx = ElabCtx::new(&env);

    let surface = parse_expr("dep_apply (fun (_ : MyBool) => MyNat) MyNat.zero")
        .map_err(|e| ElabError::ParseError(e.to_string()))
        .unwrap();

    let result = ctx.elaborate(&surface);

    assert!(
        result.is_ok(),
        "Motive beta-reduction should allow unification: {:?}",
        result.err()
    );

    // The result should be an application of dep_apply
    let expr = result.unwrap();
    match expr.kind() {
        ExprKind::App(f, _) => {
            // Inner application should have dep_apply somewhere
            fn contains_dep_apply(e: &Expr) -> bool {
                match e.kind() {
                    ExprKind::Const(n, _) => n.to_string() == "dep_apply",
                    ExprKind::App(f, a) => contains_dep_apply(f) || contains_dep_apply(a),
                    _ => false,
                }
            }
            assert!(
                contains_dep_apply(f),
                "Result should contain dep_apply application, got: {:?}",
                expr
            );
        }
        _ => panic!(
            "Expected application expression from dep_apply, got: {:?}",
            expr
        ),
    }
}

#[test]
fn test_issue796_q_pattern_as_alias_static_match() {
    let code = r#"
match q(Type) with
| whole@q($x) => whole
| _ => q(Prop)
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Static q-match with As alias should elaborate: {:?}",
        result.err()
    );
}

#[test]
fn test_issue796_q_pattern_as_alias_runtime_match() {
    let code = r#"
fun (e : Type) =>
  match e with
  | whole@q($x) => whole
  | _ => e
"#;
    let result = elab(code);
    assert!(
        result.is_ok(),
        "Runtime q-match with As alias should elaborate: {:?}",
        result.err()
    );
}
