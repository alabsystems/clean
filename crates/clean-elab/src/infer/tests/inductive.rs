// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Inductive type elaboration tests

use super::*;

#[test]
fn test_elab_inductive_simple() {
    // Simple inductive with no parameters
    let result = elab_decl(
        r"inductive Bool : Type
| false : Bool
| true : Bool",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("Bool"));
            assert_eq!(num_params, 0);
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, Name::from_string("Bool.false"));
            assert_eq!(constructors[1].0, Name::from_string("Bool.true"));
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_with_parameter() {
    // Inductive with a type parameter
    let result = elab_decl(
        r"inductive Option (α : Type) : Type
| none : Option α
| some : α → Option α",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("Option"));
            assert_eq!(num_params, 1);
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, Name::from_string("Option.none"));
            assert_eq!(constructors[1].0, Name::from_string("Option.some"));
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_recursive() {
    // Recursive inductive (like Nat)
    let result = elab_decl(
        r"inductive MyNat : Type
| zero : MyNat
| succ : MyNat → MyNat",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("MyNat"));
            assert_eq!(num_params, 0);
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, Name::from_string("MyNat.zero"));
            assert_eq!(constructors[1].0, Name::from_string("MyNat.succ"));
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_list() {
    // List type with two parameters (recursive)
    let result = elab_decl(
        r"inductive List (α : Type) : Type
| nil : List α
| cons : α → List α → List α",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("List"));
            assert_eq!(num_params, 1);
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, Name::from_string("List.nil"));
            assert_eq!(constructors[1].0, Name::from_string("List.cons"));
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_issue796_inductive_parenthesized_type_level_result() {
    let result = elab_decl(
        r"inductive Imf {α : Type u} {β : Type v} (f : α → β) : β → Type (max u v)
| mk : (a : α) → Imf f (f a)",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            universe_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("Imf"));
            assert_eq!(num_params, 3, "α, β, and f should be parameters");
            assert_eq!(constructors.len(), 1, "Imf should have one constructor");
            assert_eq!(constructors[0].0, Name::from_string("Imf.mk"));
            assert_eq!(
                universe_params,
                vec![Name::from_string("u"), Name::from_string("v")],
                "expected auto-bound universe params from `Type u` / `Type v` / `Type (max u v)`"
            );
        }
        other => panic!("expected Inductive result for Imf, got {other:?}"),
    }
}

#[test]
fn test_issue796_inductive_scopes_header_and_ctor_auto_implicits() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let result = ctx
        .elab_decl(
            &parse_decl_for_elab(
                r"inductive Cover : (x y z : List α) -> Type u
| done  : Cover [] [] []
| left  : Cover x y z -> Cover (t :: x) y (t :: z)
| right : Cover x y z -> Cover x (t :: y) (t :: z)
| both  : Cover x y z -> Cover (t :: x) (t :: y) (t :: z)",
            )
            .unwrap(),
        )
        .unwrap();

    match result {
        ElabResult::Inductive {
            num_params,
            ty,
            constructors,
            ..
        } => {
            assert_eq!(
                num_params, 1,
                "Cover should only promote header-level α to an inductive parameter; x/y/z/t stay constructor-local"
            );
            assert!(
                !ty.has_fvar_quick(),
                "inductive type should not leak free variables: {ty:?}"
            );
            assert_eq!(constructors.len(), 4);
            for (ctor_name, ctor_ty) in constructors {
                assert!(
                    !ctor_ty.has_fvar_quick(),
                    "constructor {ctor_name:?} should not leak free variables: {ctor_ty:?}"
                );
            }
        }
        other => panic!("expected Inductive result for Cover, got {other:?}"),
    }
}

#[test]
fn test_file_1616_rejects_unresolved_constructor_parameter_types() {
    let mut env = Environment::with_prelude();

    let cover = parse_decl_for_elab(
        r"inductive Cover : (x y z : List α) -> Type u
| done  : Cover [] [] []
| left  : Cover x y z -> Cover (t :: x) y (t :: z)
| right : Cover x y z -> Cover x (t :: y) (t :: z)
| both  : Cover x y z -> Cover (t :: x) (t :: y) (t :: z)",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &cover)
        .expect("Cover should elaborate and register with scoped auto-implicits");

    let linear = parse_decl_for_elab(
        r"inductive Linear : Cover x y z -> Prop
| done : Linear .done
| left : Linear c -> Linear (.left c)
| right : Linear c -> Linear (.right c)",
    )
    .unwrap();
    let err = crate::elaborate_decl_and_register(&mut env, &linear)
        .expect_err("Lean rejects unresolved implicits in auto-bound c's type");
    assert!(
        err.to_string()
            .contains("cannot synthesize implicit arguments"),
        "unexpected error: {err}"
    );
    assert!(env.get_const(&Name::from_string("Linear")).is_none());
}

// ===========================================
// Parameterized indexed inductive tests (#804)
// ===========================================

#[test]
fn test_elab_inductive_eq_parameterized() {
    // Eq with A as parameter, a/b as indices
    // Similar to Lean 4 pattern but using Type instead of Prop for simplicity.
    let result = elab_decl(
        r"inductive Eq (A : Type) : A → A → Type
| refl : forall (a : A), Eq A a a",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ty,
            ..
        } => {
            assert_eq!(name, Name::from_string("Eq"));
            // A is a parameter (before :), so num_params = 1
            assert_eq!(num_params, 1);
            // Should have one constructor: Eq.refl
            assert_eq!(constructors.len(), 1);
            assert_eq!(constructors[0].0, Name::from_string("Eq.refl"));

            // The type should be: (A : Type) → A → A → Type
            // i.e., a Pi with 3 arguments total
            let mut pi_count = 0;
            let mut current = &ty;
            while let ExprKind::Pi(_, _, body) = current.kind() {
                pi_count += 1;
                current = body;
            }
            assert_eq!(
                pi_count, 3,
                "Expected 3 Pi binders for (A : Type) → A → A → Type"
            );
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_eq_parameterized_with_bare_constructor_binder() {
    let result = elab_decl(
        r"inductive Eq (A : Type) : A → A → Type
| refl a : Eq A a a",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("Eq"));
            assert_eq!(num_params, 1);
            assert_eq!(constructors.len(), 1);
            assert_eq!(constructors[0].0, Name::from_string("Eq.refl"));

            let ctor_ty = &constructors[0].1;
            let mut pi_count = 0;
            let mut current = ctor_ty;
            while let ExprKind::Pi(_, _, body) = current.kind() {
                pi_count += 1;
                current = body;
            }
            assert_eq!(
                pi_count, 2,
                "Eq.refl should have 2 Pi binders: {{A}} and the constructor-local a, got {pi_count}"
            );
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_and_parameterized() {
    // And with A, B as parameters (no indices)
    // inductive And (A : Type) (B : Type) : Type | intro : A → B → And A B
    let result = elab_decl(
        r"inductive And (A : Type) (B : Type) : Type
| intro (a : A) (b : B) : And A B",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ty,
            ..
        } => {
            assert_eq!(name, Name::from_string("And"));
            // A and B are parameters (before :), so num_params = 2
            assert_eq!(num_params, 2);
            // Should have one constructor: And.intro
            assert_eq!(constructors.len(), 1);
            assert_eq!(constructors[0].0, Name::from_string("And.intro"));

            // The type should be: (A : Type) → (B : Type) → Type
            // i.e., a Pi with 2 arguments total
            let mut pi_count = 0;
            let mut current = &ty;
            while let ExprKind::Pi(_, _, body) = current.kind() {
                pi_count += 1;
                current = body;
            }
            assert_eq!(
                pi_count, 2,
                "Expected 2 Pi binders for (A : Type) → (B : Type) → Type"
            );
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_bool_simple() {
    // Bool as a simple enumeration (no parameters, no indices)
    let result = elab_decl(
        r"inductive MyBool : Type
| true : MyBool
| false : MyBool",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ty,
            ..
        } => {
            assert_eq!(name, Name::from_string("MyBool"));
            assert_eq!(num_params, 0);
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, Name::from_string("MyBool.true"));
            assert_eq!(constructors[1].0, Name::from_string("MyBool.false"));

            // The type should be just Type (no Pi binders)
            let mut pi_count = 0;
            let mut current = &ty;
            while let ExprKind::Pi(_, _, body) = current.kind() {
                pi_count += 1;
                current = body;
            }
            assert_eq!(pi_count, 0, "Expected 0 Pi binders for : Type");
        }
        _ => panic!("expected Inductive"),
    }
}

// ===========================================
// Inductive deriving tests
// ===========================================

#[test]
fn test_elab_inductive_with_deriving_single() {
    let result = elab_decl(
        r"inductive Bool : Type
| false : Bool
| true : Bool
deriving BEq",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            derived_instances,
            ..
        } => {
            assert_eq!(name, Name::from_string("Bool"));
            assert_eq!(derived_instances.len(), 1);
            assert_eq!(derived_instances[0].name, Name::from_string("instBoolBEq"));
            assert_eq!(derived_instances[0].class_name, Name::from_string("BEq"));
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_with_deriving_multiple() {
    // Repr and Hashable are absent from the bare environment: each is a hard
    // error, never a silent skip — reported beside `Color`, which Lean
    // declares before running any handler. Both handlers log rather than
    // throw in Lean, so the clause runs to its end.
    let (result, errors) = type_with_failed_deriving(elab_decl(
        r"inductive Color : Type
| red : Color
| green : Color
| blue : Color
deriving BEq, Repr, Hashable",
    ));
    assert_eq!(errors.len(), 2, "{errors:?}");
    for (error, class) in errors.iter().zip(["Repr", "Hashable"]) {
        assert!(
            matches!(error, ElabError::Unsupported { feature }
                if feature.contains(class) && feature.contains("never silently skipped")),
            "{error:?}"
        );
    }

    match result {
        ElabResult::Inductive {
            name,
            derived_instances,
            ..
        } => {
            assert_eq!(name, Name::from_string("Color"));
            assert_eq!(derived_instances.len(), 1);

            let class_names: Vec<_> = derived_instances
                .iter()
                .map(|d| d.class_name.clone())
                .collect();
            assert!(class_names.contains(&Name::from_string("BEq")));
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_deriving_inhabited() {
    // Over the prelude: the handler synthesizes field instances and
    // kernel-checks the instance against `Inhabited`, which a bare
    // environment does not declare (Lean's handler needs it too).
    let result = elab_decl_with_prelude(
        r"inductive MyBool : Type
| false : MyBool
| true : MyBool
deriving Inhabited",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            derived_instances,
            ..
        } => {
            assert_eq!(name, Name::from_string("MyBool"));
            assert_eq!(derived_instances.len(), 1);
            assert_eq!(
                derived_instances[0].name,
                Name::from_string("instMyBoolInhabited")
            );
            assert_eq!(
                derived_instances[0].class_name,
                Name::from_string("Inhabited")
            );

            // Check that the instance uses the first constructor (MyBool.false)
            match derived_instances[0].val.kind() {
                ExprKind::App(_, arg) => {
                    // arg should be MyBool.false
                    match arg.kind() {
                        ExprKind::Const(ctor_name, _) => {
                            assert_eq!(*ctor_name, Name::from_string("MyBool.false"));
                        }
                        _ => panic!("Expected Const for default value"),
                    }
                }
                _ => panic!("Expected App for Inhabited.mk"),
            }
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_deriving_decidable_eq() {
    let result = elab_decl(
        r"inductive Bool : Type
| false : Bool
| true : Bool
deriving DecidableEq",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            derived_instances,
            ..
        } => {
            assert_eq!(name, Name::from_string("Bool"));
            assert_eq!(derived_instances.len(), 1);
            assert_eq!(
                derived_instances[0].name,
                Name::from_string("instBoolDecidableEq")
            );
            assert_eq!(
                derived_instances[0].class_name,
                Name::from_string("DecidableEq")
            );
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_without_deriving() {
    let result = elab_decl(
        r"inductive Bool : Type
| false : Bool
| true : Bool",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            assert!(derived_instances.is_empty());
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_single_ctor_deriving() {
    // Single constructor inductive always has equal elements. Over the
    // prelude, which declares the classes the handlers build instances of.
    let result = elab_decl_with_prelude(
        r"inductive MyUnit : Type
| unit : MyUnit
deriving BEq, Inhabited",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            derived_instances,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("MyUnit"));
            assert_eq!(constructors.len(), 1);
            assert_eq!(derived_instances.len(), 2);
        }
        _ => panic!("expected Inductive"),
    }
}

// Note: Recursor tests have been moved to the kernel (clean-kernel/src/tc.rs)
// since recursor generation is now handled entirely by the kernel.
// The elaborator tests below verify basic inductive elaboration works.

#[test]
fn test_elab_inductive_simple_enum() {
    // Test elaboration of a simple enum (recursor tested in kernel)
    let result = elab_decl(
        r"inductive Bool : Type
| false : Bool
| true : Bool",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("Bool"));
            assert_eq!(num_params, 0);
            assert_eq!(constructors.len(), 2);
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_single_ctor() {
    // Test elaboration of single constructor type
    let result = elab_decl(
        r"inductive Unit : Type
| unit : Unit",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name, constructors, ..
        } => {
            assert_eq!(name, Name::from_string("Unit"));
            assert_eq!(constructors.len(), 1);
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_with_constructor_args() {
    // Test elaboration of inductive with constructor arguments
    let result = elab_decl(
        r"inductive Option (α : Type) : Type
| none : Option α
| some : α → Option α",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("Option"));
            assert_eq!(num_params, 1); // α
            assert_eq!(constructors.len(), 2);
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_elab_inductive_recursive_type() {
    // Test elaboration of a recursive inductive type
    let result = elab_decl(
        r"inductive MyNat : Type
| zero : MyNat
| succ : MyNat → MyNat",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            name,
            num_params,
            constructors,
            ..
        } => {
            assert_eq!(name, Name::from_string("MyNat"));
            assert_eq!(num_params, 0);
            assert_eq!(constructors.len(), 2);
        }
        _ => panic!("expected Inductive"),
    }
}

#[test]
fn test_decidable_eq_inductive_ne_proof_binder_type() {
    // Regression: ne_proof lambda used bare Eq constant as binder type instead of @Eq IndType a b
    let result = elab_decl(
        r"inductive Color : Type
| red : Color
| blue : Color
deriving DecidableEq",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            assert_eq!(derived_instances.len(), 1);
            let val = &derived_instances[0].val;

            // Structure: λ (a : Color) (b : Color) => casesOn ...
            // (DecidableEq is a definition, not a structure — no .mk wrapper)
            // λ (a : Color) => ...
            let inner_lam = match val.kind() {
                ExprKind::Lam(_, _, body) => body.as_ref(),
                _ => panic!("expected outer lambda"),
            };
            // λ (b : Color) => casesOn ...
            let body = match inner_lam.kind() {
                ExprKind::Lam(_, _, body) => body.as_ref(),
                _ => panic!("expected inner lambda"),
            };

            // Find the ne_proof lambda by searching for isFalse applications.
            // body is: casesOn bvar(1) arm0 arm1
            // arm0 is: casesOn bvar(0) (isTrue refl) (isFalse ne_proof)
            fn find_is_false_arg(e: &Expr) -> Option<&Expr> {
                match e.kind() {
                    ExprKind::App(f, arg) => {
                        // Check if f is App(isFalse, eq_prop) — fully applied implicit
                        // @Decidable.isFalse eq_prop ne_proof (#2461 F4)
                        if let ExprKind::App(inner_f, _eq_prop) = f.kind() {
                            if let ExprKind::Const(name, _) = inner_f.kind() {
                                if name.to_string().contains("isFalse") {
                                    return Some(arg.as_ref());
                                }
                            }
                        }
                        // Recurse into both f and arg
                        find_is_false_arg(f).or_else(|| find_is_false_arg(arg))
                    }
                    ExprKind::Lam(_, _, body) => find_is_false_arg(body),
                    _ => None,
                }
            }

            let ne_proof = find_is_false_arg(body).expect("should find isFalse(ne_proof)");

            // #3432: monomorphic multi-ctor enum body is now `casesOn`-based
            // with concrete ctor constants at each leaf. The inner `isFalse`
            // minor for `a = c_i, b = c_j (i ≠ j)` has binder type
            //   `@Eq Color Color.<c_i> Color.<c_j>`
            // (not `@Eq Color bvar(1) bvar(0)` as in the pre-#3431 attempt).
            // What we actually want to check is:
            //   1. binder_ty is fully applied `@Eq Color <a> <b>` — NOT bare
            //      `Eq` (that was the original #1917 bug).
            //   2. `a` and `b` are each closed term (Const for nullary ctors,
            //      or BVar in earlier buggy shapes we want to reject).
            match ne_proof.kind() {
                ExprKind::Lam(_, binder_ty, _) => {
                    match binder_ty.kind() {
                        ExprKind::App(eq_color_a, b) => {
                            // `b` at this point MUST be a closed ctor
                            // constant (e.g. `Color.blue`). The old buggy
                            // body left it as bvar(0) or made the binder
                            // type a bare `Eq` constant — both are regressions.
                            assert!(
                                matches!(b.kind(), ExprKind::Const(_, _)),
                                "expected ctor constant for b (e.g. Color.blue), got {:?}",
                                b.kind()
                            );
                            match eq_color_a.kind() {
                                ExprKind::App(eq_color, a) => {
                                    assert!(
                                        matches!(a.kind(), ExprKind::Const(_, _)),
                                        "expected ctor constant for a (e.g. Color.red), \
                                         got {:?}",
                                        a.kind()
                                    );
                                    match eq_color.kind() {
                                        ExprKind::App(eq, color) => {
                                            assert!(
                                                matches!(eq.kind(), ExprKind::Const(_, _)),
                                                "expected Eq constant, got {:?}",
                                                eq.kind()
                                            );
                                            assert!(
                                                matches!(color.kind(), ExprKind::Const(_, _)),
                                                "expected Color constant, got {:?}",
                                                color.kind()
                                            );
                                        }
                                        other => panic!("expected App(Eq, Color), got {:?}", other),
                                    }
                                }
                                other => panic!("expected App(App(Eq, Color), a), got {:?}", other),
                            }
                        }
                        ExprKind::Const(name, _) => {
                            panic!(
                                "BUG: ne_proof binder type is bare {name:?} constant, \
                                 should be @Eq Color <c_i> <c_j>"
                            );
                        }
                        other => panic!("expected fully-applied @Eq Color a b, got {:?}", other),
                    }
                }
                _ => panic!("ne_proof should be a lambda"),
            }
        }
        _ => panic!("expected Inductive"),
    }
}

/// Regression test #2461 F4: Decidable.isTrue in derive module must include
/// the implicit {p : Prop} argument. Bare `Decidable.isTrue Eq.refl` is ill-typed;
/// correct form is `@Decidable.isTrue (@Eq IndType a b) (@Eq.refl IndType a)`.
#[test]
fn test_decidable_eq_inductive_is_true_has_implicit_prop_arg() {
    let result = elab_decl(
        r"inductive Color : Type
| red : Color
| blue : Color
deriving DecidableEq",
    )
    .unwrap();

    match result {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            assert_eq!(derived_instances.len(), 1);
            let val = &derived_instances[0].val;

            // Find isTrue application: @Decidable.isTrue eq_prop eq_refl
            fn find_is_true_args(e: &Expr) -> Option<(&Expr, &Expr)> {
                match e.kind() {
                    ExprKind::App(f, arg) => {
                        // Check if f is App(isTrue_const, eq_prop)
                        if let ExprKind::App(inner_f, eq_prop) = f.kind() {
                            if let ExprKind::Const(name, _) = inner_f.kind() {
                                if name.to_string().contains("isTrue") {
                                    return Some((eq_prop.as_ref(), arg.as_ref()));
                                }
                            }
                        }
                        find_is_true_args(f).or_else(|| find_is_true_args(arg))
                    }
                    ExprKind::Lam(_, t, b) => find_is_true_args(t).or_else(|| find_is_true_args(b)),
                    _ => None,
                }
            }

            let (eq_prop, eq_refl) =
                find_is_true_args(val).expect("should find @Decidable.isTrue eq_prop eq_refl");

            // eq_prop must be @Eq Color bvar(1) bvar(0), not bare Eq
            match eq_prop.kind() {
                ExprKind::App(_, _) => {} // fully applied — good
                ExprKind::Const(name, _) => {
                    panic!(
                        "BUG: isTrue implicit arg is bare {:?} constant, \
                         should be @Eq Color bvar(1) bvar(0)",
                        name
                    );
                }
                other => panic!("expected fully-applied @Eq, got {:?}", other),
            }

            // eq_refl must be @Eq.refl Color bvar(1), not bare Eq.refl
            match eq_refl.kind() {
                ExprKind::App(_, _) => {} // fully applied — good
                ExprKind::Const(name, _) => {
                    panic!(
                        "BUG: isTrue proof arg is bare {:?} constant, \
                         should be @Eq.refl Color bvar(1)",
                        name
                    );
                }
                other => panic!("expected fully-applied @Eq.refl, got {:?}", other),
            }
        }
        _ => panic!("expected Inductive"),
    }
}

/// Regression test #2001: elaborate And with binder-style constructors and
/// register via add_inductive. Previously the parser dropped constructor
/// binders (e.g., `(a : A) (b : B)` in `| intro (a : A) (b : B) : And A B`),
/// producing a malformed constructor type that failed kernel type-checking.
#[test]
fn test_elab_and_register_add_inductive_2001() {
    use clean_kernel::inductive::{Constructor, InductiveDecl, InductiveType};

    let mut env = Environment::new();
    let result = {
        let mut ctx = ElabCtx::new(&env);
        let surface = clean_parser::parse_decl(
            r"inductive And (A : Type) (B : Type) : Type
| intro (a : A) (b : B) : And A B",
        )
        .unwrap();
        ctx.elab_decl(&surface).unwrap()
    };

    match &result {
        ElabResult::Inductive {
            name,
            universe_params,
            num_params,
            ty,
            constructors,
            ..
        } => {
            assert_eq!(*num_params, 2);
            assert_eq!(constructors.len(), 1);
            assert_eq!(constructors[0].0, Name::from_string("And.intro"));

            // The constructor type must include the field binders.
            // Before #2001 fix: {A : Type} → {B : Type} → And (missing fields!)
            // After fix: {A : Type} → {B : Type} → A → B → And A B
            let ctor_ty = &constructors[0].1;
            let mut pi_count = 0;
            let mut current = ctor_ty;
            while let ExprKind::Pi(_, _, body) = current.kind() {
                pi_count += 1;
                current = body;
            }
            assert_eq!(
                pi_count, 4,
                "And.intro should have 4 Pi binders: {{A}} {{B}} (a) (b), got {pi_count}"
            );

            // Register with the kernel — this is the step that failed before
            let decl = InductiveDecl {
                level_params: universe_params.clone(),
                num_params: *num_params,
                types: vec![InductiveType {
                    name: name.clone(),
                    type_: ty.clone(),
                    constructors: constructors
                        .iter()
                        .map(|(n, t)| Constructor {
                            name: n.clone(),
                            type_: t.clone(),
                        })
                        .collect(),
                }],
            };
            env.add_inductive(decl)
                .expect("add_inductive should succeed for And (#2001)");
        }
        _ => panic!("expected Inductive"),
    }
}

/// Pattern matching on a restored nested inductive type should resolve to the
/// parent type and declared container spelling (#3406).
///
/// ```lean
/// inductive Value where
///   | int : Nat -> Nat -> Value
///   | float : Nat -> Value
///   | bool : Bool -> Value
///   | ptr : Nat -> Value
///   | nullPtr : Value
///   | undef : Value
///   | aggregate : List Value -> Value
///
/// def Value.isPtr : Value -> Bool
///   | Value.ptr _ => true
///   | _ => false
/// ```
///
/// The `aggregate` constructor triggers internal nested elimination, followed by
/// restore: temporary mirror names are erased, the constructor exposes
/// `List Value`, and companion recursion remains under `Value.rec_1`.
#[test]
fn test_issue3406_nested_inductive_match_resolves_parent_type() {
    let mut env = Environment::with_prelude();

    // Register the Value inductive (with nested List Value)
    let value_decl = parse_decl_for_elab(
        r"inductive Value where
  | int : Nat -> Nat -> Value
  | float : Nat -> Value
  | bool : Bool -> Value
  | ptr : Nat -> Value
  | nullPtr : Value
  | undef : Value
  | aggregate : List Value -> Value",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &value_decl)
        .expect("Value inductive with nested List should register");

    // Verify the post-restore artifact model rather than the temporary mirror.
    assert!(
        env.get_inductive(&Name::from_string("Value._List"))
            .is_none(),
        "temporary Value._List must be erased after nested restore"
    );
    assert!(
        env.get_recursor(&Name::from_string("Value.rec_1"))
            .is_some(),
        "restored companion recursion must remain as Value.rec_1"
    );
    fn mentions_const(expr: &Expr, target: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name.to_string() == target,
            ExprKind::App(f, a) => mentions_const(f, target) || mentions_const(a, target),
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                mentions_const(ty, target) || mentions_const(body, target)
            }
            _ => false,
        }
    }
    let aggregate = env
        .get_constructor(&Name::from_string("Value.aggregate"))
        .expect("restored aggregate constructor");
    assert!(mentions_const(&aggregate.type_, "List"));
    assert!(!mentions_const(&aggregate.type_, "Value._List"));

    // Test 1: Simple pattern match on Value (the exact repro from #3406)
    let isptr_decl = parse_decl_for_elab(
        r"def Value.isPtr : Value -> Bool
  | Value.ptr _ => true
  | _ => false",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &isptr_decl)
        .expect("Value.isPtr pattern match should elaborate and register (issue #3406)");

    // Test 2: Match that includes the aggregate constructor (uses nested List Value)
    let is_aggregate_decl = parse_decl_for_elab(
        r"def Value.isAggregate : Value -> Bool
  | Value.aggregate _ => true
  | _ => false",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &is_aggregate_decl)
        .expect("Value.isAggregate matching aggregate ctor should elaborate (issue #3406)");

    // Test 3: Full exhaustive match on all constructors
    let to_nat_decl = parse_decl_for_elab(
        r"def Value.toNat : Value -> Nat
  | Value.int n _ => n
  | Value.float n => n
  | Value.bool _ => 0
  | Value.ptr n => n
  | Value.nullPtr => 0
  | Value.undef => 0
  | Value.aggregate _ => 0",
    )
    .unwrap();
    crate::elaborate_decl_and_register(&mut env, &to_nat_decl)
        .expect("Value.toNat exhaustive match should elaborate (issue #3406)");
}

// ---------------------------------------------------------------------------
// Task 4 slice 1: indexed-family ELIMINATION over a variable index.
//
// `Vec α n` is a genuine indexed family (`n : Nat` is an INDEX, not a
// parameter). Its `cons` constructor carries an IMPLICIT index-witness field
// `{n : Nat}` that is NOT written in a pattern — it is solved by index
// unification. Matching `Vec.cons x rest` therefore supplies 2 explicit
// patterns for a 3-field constructor; the elaborator must auto-insert a
// wildcard at the implicit field position. Before this slice the arity check
// counted the implicit field, rejecting the match with
// ConstructorPatternArityMismatch { expected: 3, actual: 2 }.
//
// These tests gate on the KERNEL: `elaborate_decl_and_register` runs the full
// kernel type-check (strict-enforce defaults on), so a green result means the
// lowered casesOn term is well-typed, not merely that elaboration succeeded.

/// Helper: register `Vec α : Nat → Type` with `nil`/`cons` into a prelude env.
fn register_vec_family(env: &mut Environment) {
    let vec_decl = parse_decl_for_elab(
        r"inductive Vec (α : Type) : Nat → Type
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)",
    )
    .expect("Vec indexed family should parse");
    crate::elaborate_decl_and_register(env, &vec_decl)
        .expect("Vec indexed family should elaborate and register");
}

#[test]
fn test_task4_indexed_match_implicit_field_both_arms_kernel_checks() {
    let mut env = Environment::with_prelude();
    register_vec_family(&mut env);

    // Both arms over a *variable* index `n`. `Vec.cons _ _` supplies two
    // explicit patterns for the three-field `cons` (the implicit `{n}` index
    // witness is auto-wildcarded). Must elaborate AND pass the kernel.
    let is_empty = parse_decl_for_elab(
        r"def Vec.isEmpty {α : Type} {n : Nat} (v : Vec α n) : Bool :=
  match v with
  | Vec.nil => true
  | Vec.cons _ _ => false",
    )
    .expect("Vec.isEmpty should parse");
    crate::elaborate_decl_and_register(&mut env, &is_empty).expect(
        "Vec.isEmpty: implicit index-witness field must auto-wildcard and the \
         lowered casesOn must pass the kernel type-check",
    );
}

#[test]
fn test_task4_indexed_match_binds_explicit_fields_kernel_checks() {
    let mut env = Environment::with_prelude();
    register_vec_family(&mut env);

    // The `cons` arm names BOTH explicit fields (`x : α`, `rest : Vec α n`) and
    // uses the head in the body, exercising that the explicit patterns bind to
    // the correct fields once the implicit `{n}` field is skipped.
    let head_or = parse_decl_for_elab(
        r"def Vec.headOr {α : Type} {n : Nat} (default : α) (v : Vec α n) : α :=
  match v with
  | Vec.nil => default
  | Vec.cons x _ => x",
    )
    .expect("Vec.headOr should parse");
    crate::elaborate_decl_and_register(&mut env, &head_or).expect(
        "Vec.headOr: explicit fields must bind past the implicit index field and \
         the lowered casesOn must pass the kernel type-check",
    );
}

#[test]
fn test_task4_indexed_match_wrong_explicit_arity_still_errors() {
    let mut env = Environment::with_prelude();
    register_vec_family(&mut env);

    // ADVERSARIAL: `Vec.cons a b c` writes THREE explicit patterns. `cons` has
    // only TWO explicit fields (the `{n}` index witness is implicit), so this is
    // a genuine arity error. The narrowed check must still reject it — the check
    // is narrowed (to the explicit-field count), never removed.
    let bad = parse_decl_for_elab(
        r"def Vec.bad {α : Type} {n : Nat} (v : Vec α n) : Bool :=
  match v with
  | Vec.nil => true
  | Vec.cons a b c => false",
    )
    .expect("Vec.bad should parse");
    let result = crate::elaborate_decl_and_register(&mut env, &bad);
    assert!(
        matches!(
            result,
            Err(ElabError::ConstructorPatternArityMismatch {
                ref ctor_name,
                expected: 2,
                actual: 3,
                ..
            }) if ctor_name == "Vec.cons"
        ),
        "Vec.cons a b c (3 explicit patterns, 2 explicit fields) must still error \
         with a narrowed arity mismatch (expected 2, actual 3), got {result:?}"
    );
}

#[test]
fn test_task4_indexed_match_no_implicit_field_ctor_unchanged() {
    let mut env = Environment::with_prelude();
    register_vec_family(&mut env);

    // The `nil` constructor has zero fields; this nullary arm must keep working
    // exactly as before (no expansion, no spurious arity error). Also asserts a
    // single-arm extraction over the all-explicit shape is unaffected.
    let only_nil = parse_decl_for_elab(
        r"def Vec.isNil {α : Type} {n : Nat} (v : Vec α n) : Bool :=
  match v with
  | Vec.nil => true
  | Vec.cons _ _ => false",
    )
    .expect("Vec.isNil should parse");
    crate::elaborate_decl_and_register(&mut env, &only_nil)
        .expect("Vec.isNil nullary arm must remain kernel-checkable");
}

// ---------------------------------------------------------------------------
// Track A: `deriving BEq` on a nullary enum must use the kernel-correct
// casesOn argument order (`casesOn motive minors… major`) and supply the
// implicit type argument to `BEq.mk` / `BEq.beq`. Before the fix the scrutinee
// was placed in a minor-premise slot, producing "expected (motive C), got T"
// kernel mismatches. This verifies the derived instance passes strict kernel
// type checking and has an empty axiom closure (no sorry).
// ---------------------------------------------------------------------------
#[test]
fn test_track_a_beq_enum_strict_kernel_and_axiom_free() {
    let mut env = Environment::with_prelude();
    let decl =
        parse_decl_for_elab("inductive SR where\n  | Bitset : SR\n  | Boxed : SR\nderiving BEq")
            .unwrap();
    let result = crate::elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_ok(),
        "enum SR deriving BEq should elaborate+register: {:?}",
        result.err()
    );

    let inst = match result.unwrap() {
        ElabResult::Inductive {
            derived_instances, ..
        } => derived_instances
            .into_iter()
            .find(|i| i.class_name == Name::from_string("BEq"))
            .expect("should have BEq derived instance"),
        other => panic!("expected Inductive, got {other:?}"),
    };

    // Strict kernel type check against a fresh env with only the bare enum.
    let mut env2 = Environment::with_prelude();
    let decl2 = parse_decl_for_elab("inductive SR where\n  | Bitset : SR\n  | Boxed : SR").unwrap();
    crate::elaborate_decl_and_register(&mut env2, &decl2).expect("bare SR should register");

    let inst_decl = Declaration::Definition {
        name: inst.name.clone(),
        level_params: inst.level_params.clone(),
        type_: inst.ty.clone(),
        value: inst.val.clone(),
        is_reducible: true,
    };
    let add_result = env2.add_decl(inst_decl);
    assert!(
        add_result.is_ok(),
        "enum BEq instance must pass strict kernel type check (infer_type): {:?}",
        add_result.err()
    );

    let deps = env2
        .axiom_deps(&Name::from_string("instSRBEq"))
        .expect("instSRBEq is registered, axiom_deps should return Some");
    let dep_names: Vec<String> = deps.iter().map(|n| n.to_string()).collect();
    assert!(
        dep_names.is_empty(),
        "enum BEq instance must have empty axiom closure, got {dep_names:?}"
    );
}

#[test]
fn test_recursive_repr_is_materialized_from_registered_constructor_metadata() {
    fn mentions_const(expr: &Expr, expected: &str) -> bool {
        match expr.kind() {
            ExprKind::Const(name, _) => name == &Name::from_string(expected),
            ExprKind::App(fun, arg) => {
                mentions_const(fun, expected) || mentions_const(arg, expected)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                mentions_const(ty, expected) || mentions_const(body, expected)
            }
            ExprKind::Let(_, ty, value, body, _) => {
                mentions_const(ty, expected)
                    || mentions_const(value, expected)
                    || mentions_const(body, expected)
            }
            _ => false,
        }
    }

    fn mentions_string(expr: &Expr, expected: &str) -> bool {
        match expr.kind() {
            ExprKind::Lit(Literal::String(value)) => value.as_ref() == expected,
            ExprKind::App(fun, arg) => {
                mentions_string(fun, expected) || mentions_string(arg, expected)
            }
            ExprKind::Lam(_, ty, body) | ExprKind::Pi(_, ty, body) => {
                mentions_string(ty, expected) || mentions_string(body, expected)
            }
            ExprKind::Let(_, ty, value, body, _) => {
                mentions_string(ty, expected)
                    || mentions_string(value, expected)
                    || mentions_string(body, expected)
            }
            _ => false,
        }
    }

    let source =
        "inductive ReprTree where\n  | leaf : ReprTree\n  | next : ReprTree -> ReprTree\nderiving Repr";
    let elaborated = elab_decl_with_prelude(source)
        .expect("recursive deriving Repr should materialize during elaboration");
    let public_value = match &elaborated {
        ElabResult::Inductive {
            derived_instances, ..
        } => {
            &derived_instances
                .iter()
                .find(|instance| instance.class_name == Name::from_string("Repr"))
                .expect("public result should contain Repr")
                .val
        }
        other => panic!("expected Inductive result, got {other:?}"),
    };
    assert!(
        mentions_const(public_value, "ReprTree.casesOn")
            || mentions_const(public_value, "ReprTree.rec"),
        "public elaboration result must contain the final constructor-aware Repr: {public_value:?}"
    );

    let mut env = Environment::with_prelude();
    let decl = parse_decl_for_elab(source).expect("recursive Repr fixture should parse");
    crate::elaborate_decl_and_register(&mut env, &decl)
        .expect("recursive deriving Repr should materialize after parent registration");

    let inst_name = Name::from_string("instReprTreeRepr");
    let info = env
        .get_const(&inst_name)
        .expect("materialized Repr instance should be registered");
    let value = info
        .value
        .as_ref()
        .expect("materialized Repr instance should have a definition body");
    assert!(
        mentions_const(value, "ReprTree.casesOn") || mentions_const(value, "ReprTree.rec"),
        "final Repr value must dispatch on the registered constructor metadata: {value:?}"
    );
    // The nullary constructor renders as its name; the one with a field
    // renders through the opaque `Clean.Repr.render` — its bare name dropped
    // the argument, so `repr (next leaf) = repr (next (next leaf))` checked
    // where Lean refuses it (ledger class (90)).
    assert!(mentions_string(value, "ReprTree.leaf"));
    assert!(!mentions_string(value, "ReprTree.next"));
    assert!(mentions_const(value, "Clean.Repr.render"));
    assert!(!value.has_sorry(), "derived Repr must not contain sorry");
    let deps = env
        .axiom_deps(&inst_name)
        .expect("registered Repr instance must have an auditable closure");
    assert!(deps.is_empty(), "derived Repr must be axiom-free: {deps:?}");
}

// ── coinductive (#191): the v1 greatest-fixpoint surface ────────────────
//
// The lowering under test lives in `crate::coinductive_surface`; its
// envelope is documented there. These tests pin BOTH halves of the
// contract: the supported shape genuinely elaborates to a greatest
// fixpoint, and every shape outside the envelope still rejects loudly.

/// Prelude env plus a tiny stream model (`Str`/`shd`/`stl`) for the
/// bisimulation examples. Each declaration is elaborated and kernel-checked
/// through the ordinary path.
fn coind_stream_env() -> Environment {
    let mut env = Environment::with_prelude();
    for src in [
        r"def Str : Type := Nat → Nat",
        r"def shd (s : Str) : Nat := s 0",
        r"def stl (s : Str) : Str := fun n => s (Nat.succ n)",
    ] {
        let d = parse_decl_for_elab(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        crate::elaborate_decl_and_register(&mut env, &d)
            .unwrap_or_else(|e| panic!("elab `{src}`: {e:?}"));
    }
    env
}

fn elab_in(env: &mut Environment, src: &str) -> Result<ElabResult, ElabError> {
    let d = parse_decl_for_elab(src)?;
    crate::elaborate_decl_and_register(env, &d)
}

/// The v1 shape lands: a `coinductive` bisimulation elaborates to the gfp
/// encoding, every companion kernel-checks, and the result BEHAVES like a
/// greatest fixpoint (Park coinduction proves `Bisim s s`, which the LEAST
/// fixpoint of this functor cannot).
#[test]
fn test_elab_coinductive_lowers_to_greatest_fixpoint() {
    let mut env = coind_stream_env();
    elab_in(
        &mut env,
        r"coinductive Bisim : Str → Str → Prop
| step : shd s = shd t → Bisim (stl s) (stl t) → Bisim s t",
    )
    .expect("the v1 coinductive shape must elaborate to the gfp encoding");

    // Every companion is registered and axiom-free (no `sorry`, no new axiom).
    for name in [
        "Bisim",
        "Bisim.F",
        "Bisim.coind",
        "Bisim.F_mono",
        "Bisim.unfold",
        "Bisim.fold",
        "Bisim.step",
        "Bisim.cases",
        "Bisim.acc",
        "Bisim.coind_upto",
        "Bisim.paco",
        "Bisim.paco_coind",
        "Bisim.paco_unfold",
        "Bisim.paco_fold",
        "Bisim.paco_mon",
        "Bisim.paco_bot",
        "Bisim.le_paco",
        "Bisim.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }

    // A greatest fixpoint has NO induction principle. `Bisim` is a `def`,
    // not an inductive type, so there is no recursor to misuse.
    assert!(
        env.get_const(&Name::from_string("Bisim.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // THE discriminator. `bisimF`'s LEAST fixpoint is empty (every
    // derivation would have to be infinitely deep), so `Bisim s s` is
    // provable only if `Bisim` really is the GREATEST fixpoint.
    elab_in(
        &mut env,
        r"theorem bisim_refl : ∀ s : Str, Bisim s s :=
  fun s => Bisim.coind (fun a b => a = b)
    (fun a b h => And.intro (congrArg shd h) (congrArg stl h)) s s rfl",
    )
    .expect("Park coinduction through the generated `Bisim.coind` must prove `Bisim s s`");

    // Anti-vacuity: the destructor yields REAL content, so `Bisim` is not
    // the constantly-true predicate.
    elab_in(
        &mut env,
        r"theorem bisim_head : ∀ s : Str, ∀ t : Str, Bisim s t → shd s = shd t :=
  fun s t h => And.left (Bisim.unfold s t h)",
    )
    .expect("the generated `Bisim.unfold` must expose the non-recursive premise");

    // The declared constructor is usable at its declared type.
    elab_in(
        &mut env,
        r"theorem bisim_step_use : ∀ s : Str, ∀ t : Str,
    shd s = shd t → Bisim (stl s) (stl t) → Bisim s t :=
  fun s t h0 h1 => Bisim.step h0 h1",
    )
    .expect("the generated constructor must have the declared type");
}

/// Everything outside the v1 envelope must reject LOUDLY — naming the
/// construct and the declaration — rather than silently mint a least
/// fixpoint or a partially-registered family.
#[test]
fn test_elab_coinductive_fails_closed() {
    // (shape, a distinctive fragment of the required diagnostic)
    let out_of_envelope: &[(&str, &str)] = &[
        // Type-valued: that is the `codata` command's job, not a gfp predicate.
        (
            r"coinductive Strm : Type
| cons : Nat → Strm → Strm",
            "result sort must be `Prop`",
        ),
        // ZERO constructors: an empty disjunction would mint the
        // constantly-False predicate (Brick 1 lifted the K = 1 restriction,
        // K = 0 stays refused).
        (
            r"coinductive Nix : Str → Str → Prop",
            "at least one constructor",
        ),
        // Duplicate constructor names: the intro theorems would collide.
        (
            r"coinductive Dup : Str → Str → Prop
| step : Dup (stl s) (stl t) → Dup s t
| step : shd s = shd t → Dup s t",
            "declared more than once",
        ),
        // Per-constructor vacuity (Brick 3 rule: equations + premises ≥ 1):
        // a premise-less, equation-less SECOND constructor makes its
        // disjunct — hence the whole functor — constantly true.
        (
            r"coinductive VacTwo : Str → Prop
| step : VacTwo (stl s) → VacTwo s
| bad : VacTwo s",
            "no premises and no index equations",
        ),
        // Row-name capture: ctor `a`'s SUBSTITUTED binder `shd` (a binder
        // may shadow a constant) names the shared row after the constant
        // `shd`; ctor `b` then mentions the CONSTANT `shd` in a premise —
        // under the shared index row that occurrence would be captured.
        (
            r"coinductive Cap : Str → Str → Prop
| a (shd : Str) : Cap (stl shd) (stl t) → Cap shd t
| b : shd u = shd v → Cap (stl u) (stl v) → Cap u v",
            "would be captured",
        ),
        // α-rename shadowing: ctor `two` binds `a` inside a premise while
        // `a` is a target variable being renamed onto the shared row.
        (
            r"coinductive Shad : Str → Str → Prop
| one : shd s = shd t → Shad (stl s) (stl t) → Shad s t
| two : (∀ a : Nat, a = a) → Shad (stl a) (stl b) → Shad a b",
            "shadowing a variable of the α-rename",
        ),
        // The NEW `cases` companion suffix is reserved like the others.
        (
            r"coinductive Inv : Str → Str → Prop
| step : Inv (stl s) (stl t) → Inv s t
| cases : shd s = shd t → Inv s t",
            "collides with the generated companion",
        ),
        // The paco-rung companion suffixes (`acc`, `coind_upto`) are
        // reserved like the others.
        (
            r"coinductive Acc2 : Str → Str → Prop
| step : Acc2 (stl s) (stl t) → Acc2 s t
| acc : shd s = shd t → Acc2 s t",
            "collides with the generated companion",
        ),
        (
            r"coinductive Upto : Str → Str → Prop
| step : Upto (stl s) (stl t) → Upto s t
| coind_upto : shd s = shd t → Upto s t",
            "collides with the generated companion",
        ),
        // The paco-tower companion suffixes (`paco`, `paco_coind`,
        // `paco_unfold`, `paco_fold`, `paco_mon`, `paco_bot`, `le_paco`,
        // `paco_acc`) are reserved like the others — pinned at the tower's
        // def and its accumulation theorem.
        (
            r"coinductive PTow : Str → Str → Prop
| step : PTow (stl s) (stl t) → PTow s t
| paco : shd s = shd t → PTow s t",
            "collides with the generated companion",
        ),
        (
            r"coinductive PTow2 : Str → Str → Prop
| step : PTow2 (stl s) (stl t) → PTow2 s t
| paco_acc : shd s = shd t → PTow2 s t",
            "collides with the generated companion",
        ),
        // Compound target over an UNDECLARED variable (Brick 3 narrowed the
        // old "DISTINCT variable arguments" refusal honestly): `stl s` is a
        // legal equated target only over declared binders / substituted
        // variables / constants — `s` is none of them, and a fresh variable
        // is only bindable by substituting at a bare position. Declaring
        // `(s : Str)` makes this exact shape accept (see
        // `test_elab_coinductive_compound_target_with_declared_binder`).
        (
            r"coinductive Bad : Str → Str → Prop
| step : Bad s t → Bad (stl s) t",
            "neither an index-substituted target variable",
        ),
        // Target head/arity outside the declared predicate: the residual
        // core of the old target-shape refusal.
        (
            r"coinductive TS : Str → Prop
| step : TS (stl s) → Str",
            "must conclude in",
        ),
        // A hole in a target argument would elaborate to an
        // arbitrarily-solved metavariable inside the generated functor.
        (
            r"coinductive Hol : Str → Prop
| step : Hol (stl s) → Hol _",
            "contains a hole",
        ),
        // The predicate nested inside its own index.
        (
            r"coinductive NP : Str → Prop
| step : NP (stl s) → NP (stl (NP s))",
            "nested occurrence of the predicate",
        ),
        // A bare REGISTERED CONSTANT as a target argument: ambiguous
        // between v1's fresh-index-variable reading (which would shadow
        // it) and the constant reading `inductive` would give it — refused
        // rather than silently picking either.
        (
            r"coinductive BC : Str → Prop
| step : BC shd → BC shd",
            "is a registered constant",
        ),
        // The Brick-3 vacuity boundary from the equations side: `nil`'s
        // equations-only disjunct is LEGAL (see
        // `test_elab_coinductive_equations_only_ctor`), but `bad` has
        // neither equations nor premises and stays refused.
        (
            r"coinductive CBV : Nat → Nat → Prop
| nil : CBV 0 0
| bad : CBV m n",
            "no premises and no index equations",
        ),
        // ── declaration-parameters rung refusals ───────────────────────
        // The old blanket "declaration parameters are not supported"
        // refusal is LIFTED (`Par (n : Nat)` — the exact former battery
        // fixture — now accepts; see the `decl_param` accept tests). The
        // envelope's edges refuse by name instead:
        // Universe parameters stay refused.
        (
            r"coinductive UP.{u} : Str → Prop
| step : UP (stl s) → UP s",
            "universe-polymorphic",
        ),
        // An implicit declaration parameter.
        (
            r"coinductive IPar {f : Nat → Nat} : Str → Prop
| step : IPar f (stl s) → IPar f s",
            "is implicit/instance",
        ),
        // A parameter type mentioning the predicate itself.
        (
            r"coinductive SPar (q : SPar) : Str → Prop
| step : SPar q (stl s) → SPar q s",
            "type of declaration parameter",
        ),
        // A recursive PREMISE varying the parameter position — that would
        // be an index, not a parameter.
        (
            r"coinductive PVar (f : Nat → Nat) : Str → Prop
| step : PVar (fun n => n) (stl s) → PVar f s",
            "is not the parameter",
        ),
        // The TARGET varying the parameter position.
        (
            r"coinductive TVar (f : Nat → Nat) : Str → Prop
| step : TVar f (stl s) → TVar (fun n => n) s",
            "is not the parameter",
        ),
        // A bare parameter name in an INDEX position: ambiguous between a
        // fresh index variable (shadowing) and the parameter's value.
        (
            r"coinductive BPar (n : Nat) : Nat → Prop
| step : BPar n n → BPar n n",
            "bare declaration parameter",
        ),
        // A constructor binder shadowing a parameter name.
        (
            r"coinductive CSh (f : Nat → Nat) : Str → Prop
| step (f : Nat → Nat) : CSh f (stl s) → CSh f s",
            "shadows the declaration parameter",
        ),
        // A guard binder shadowing a parameter name (the guarded rung's
        // param-capture hazard: the shadowed row would no longer be fixed).
        (
            r"coinductive GSh (u : Str) : Str → Prop
| step : (∀ (u : Str), shd u = 0 → GSh u (stl s)) → GSh u s",
            "shadows the declaration parameter",
        ),
        // A duplicate parameter name.
        (
            r"coinductive DPar (f : Nat → Nat) (f : Nat → Nat) : Str → Prop
| step : DPar f f (stl s) → DPar f f s",
            "declaration parameter `f` twice",
        ),
        // `deriving` on a Prop-valued greatest fixpoint is meaningless.
        (
            r"coinductive Der : Str → Str → Prop
| step : Der (stl s) (stl t) → Der s t
deriving Repr",
            "deriving",
        ),
        // A constructor with no premises AND no index equations would make
        // the functor `True` (the Brick-3 vacuity rule: eqs + premises ≥ 1).
        (
            r"coinductive Vac : Str → Prop
| step : Vac s",
            "no premises and no index equations",
        ),
        // A stray free variable would be AUTO-BOUND into the functor.
        (
            r"coinductive Stray : Str → Str → Prop
| step : Stray (stl s) qUnbound → Stray s t",
            "neither a target variable nor a known constant",
        ),
        // A non-positive occurrence of the predicate: under the guarded-
        // premise rung this is analysed as a guarded clause whose HYPOTHESIS
        // mentions the predicate — refused by naming the negative position
        // (formerly the generic FULLY-APPLIED message).
        (
            r"coinductive NegP : Str → Str → Prop
| step : (NegP s t → False) → NegP s t",
            "LEFT of an arrow, a negative/non-strictly-positive occurrence",
        ),
        // A partially-applied recursive occurrence names the arity failure.
        (
            r"coinductive GP : Str → Str → Prop
| step : GP s → GP s t",
            "must be FULLY APPLIED",
        ),
        // ── guarded-premise ("P under ∀/→") refusals ───────────────────
        // P in a guard HYPOTHESIS — left of an arrow under the ∀.
        (
            r"coinductive GH : Str → Prop
| step : (∀ (q : Str), GH q → shd q = shd q) → GH s",
            "LEFT of an arrow, a negative/non-strictly-positive occurrence",
        ),
        // P in a guard BINDER TYPE — a non-strictly-positive hazard.
        (
            r"coinductive GB : Str → Prop
| step : (∀ (q : GB s), GB s) → GB s",
            "binder types under a guard must be",
        ),
        // An untyped guard binder: the envelope demands explicit types.
        (
            r"coinductive GU : Str → Prop
| step : (∀ q, shd q = shd q → GU q) → GU s",
            "guard binders must be explicitly typed",
        ),
        // P in an ∃-conclusion binder type.
        (
            r"coinductive GE : Str → Prop
| step : (∃ q : GE s, shd s = shd s) → GE s",
            "guarded premise's ∃-conclusion",
        ),
        // A conjunct under the ∃-conclusion that mentions P without being
        // the flat recursive atom.
        (
            r"coinductive GX : Str → Prop
| step : (∃ q : Str, (GX q → False)) → GX s",
            "conjunct under the `∃`-conclusion",
        ),
        // ∀ binders after the first hypothesis arrow of a guard.
        (
            r"coinductive GM : Str → Prop
| step : (∀ (q : Str), shd q = shd q → ∀ (r : Str), GM r) → GM s",
            "LEADING `∀` binders",
        ),
        // A constructor claiming a generated companion name.
        (
            r"coinductive Clash : Str → Str → Prop
| fold : Clash (stl s) (stl t) → Clash s t",
            "collides with the generated companion",
        ),
        // ── Brick 2 binder-envelope refusals ───────────────────────────
        // A binder TYPE mentioning the predicate: a nested / negative-
        // position hazard, not this rung.
        (
            r"coinductive PT : Str → Prop
| step (q : PT (stl s)) : shd s = shd s → PT s",
            "nested/negative-position hazard",
        ),
        // NOTE: the Brick-2 binder/target-overlap refusal (`Ovl`) is
        // RETIRED — Brick 3's substitution/equation split makes the shape
        // unambiguous; the exact old fixture now accepts in
        // `test_elab_coinductive_binder_substitution_target`.
        // A premise-only variable WITHOUT a declared binder keeps the
        // stray-name refusal byte-identical (`q` is declared, `r` is not
        // — the explicit binder is the deliberate tax).
        (
            r"coinductive Stray2 : Str → Prop
| step (q : Str) : shd q = shd r → Stray2 s",
            "neither a target variable nor a known constant",
        ),
        // Only LEADING binders lift: a binder after the first premise
        // arrow (a dependent premise telescope) keeps a named refusal.
        (
            r"coinductive Mid : Str → Prop
| step : shd s = shd s → (q : Str) → Mid s",
            "only LEADING explicitly-typed binders",
        ),
        // An untyped binder: the ∃ domain must be declared.
        (
            r"coinductive Unty : Str → Prop
| step q : shd q = shd q → Unty s",
            "must be explicitly typed",
        ),
        // An implicit binder: intro/cases take the binders as explicit ∀s.
        (
            r"coinductive Impl : Str → Prop
| step {q : Str} : shd q = shd q → Impl s",
            "only explicit",
        ),
        // A duplicate binder name: the ∃ nest would shadow.
        (
            r"coinductive DupB : Str → Prop
| step (q : Str) (q : Str) : shd q = shd q → DupB s",
            "declares binder `q` twice",
        ),
        // The generated-name marker is reserved.
        (
            r"coinductive Res : Str → Prop
| step (R_coind : Str) : shd R_coind = shd R_coind → Res s",
            "`_coind` marker",
        ),
        // A binder named after the SHARED index row of the first
        // constructor: the α-rename onto that row would be captured.
        (
            r"coinductive RowCap : Str → Str → Prop
| one : shd s = shd t → RowCap (stl s) (stl t) → RowCap s t
| two (s : Str) : shd u = shd s → RowCap (stl u) (stl v) → RowCap u v",
            "shared index-row name",
        ),
        // An anonymous binder: the intro theorem could not supply it as an
        // `Exists.intro` witness.
        (
            r"coinductive Anon : Str → Prop
| step (_ : Str) : shd s = shd s → Anon s",
            "anonymous binder",
        ),
        // A stray name inside a binder TYPE: the same auto-bind hazard as
        // premises, at the ∃ domain position.
        (
            r"coinductive BTS : Str → Prop
| step (q : Unknown77) : shd s = shd s → BTS s",
            "an earlier binder of this constructor",
        ),
    ];

    let base = coind_stream_env();
    for (src, needle) in out_of_envelope {
        let mut env = base.clone();
        match elab_in(&mut env, src) {
            Err(ElabError::Unsupported { feature }) => {
                assert!(
                    feature.contains("coinductive"),
                    "diagnostic must name the construct: {feature}\nfor:\n{src}"
                );
                assert!(
                    feature.contains(needle),
                    "diagnostic must explain the envelope clause \
                     (expected {needle:?}): {feature}\nfor:\n{src}"
                );
            }
            other => panic!("must fail closed with Unsupported, got {other:?}\nfor:\n{src}"),
        }
    }
}

/// BRICK 0b GOLDEN REGRESSION (`designs/2026-08-25-rank1-full-gfp-lowering.md`):
/// pins the KERNEL TYPE of all 17 declarations generated for the v1 `Bisim`
/// fixture (7 at Brick 0b; the paco/accumulation rung added `Bisim.acc` and
/// `Bisim.coind_upto`, 2026-08-26; the paco parameterized-tower rung added
/// the 8-companion `Bisim.paco` tower, 2026-08-26), so any change to the
/// generated statements fails loudly.
///
/// Pinning mechanism (documented choice): each registered type is compared
/// against a literal via the kernel `Expr` `Display` rendering. That
/// rendering is robust here — registered types are CLOSED de Bruijn terms
/// (no fvar ids can appear), and the printer derives binder names
/// deterministically from domain types (kernel `BinderData` stores no
/// names), so the literals are stable across runs and insensitive to
/// alpha-level churn in the generator. The one thing the printer collapses
/// is implicit-vs-explicit on DEPENDENT binders (`{s : Str}` and
/// `(s : Str)` both render as `(s : Str) -> …`), so each declaration
/// additionally pins its outer Pi-spine `BinderInfo` row — that is what
/// keeps `Bisim.step`'s index binders IMPLICIT.
#[test]
fn test_elab_coinductive_golden_kernel_types() {
    use clean_kernel::{BinderInfo, Expr, ExprKind};

    /// Binder infos of the outer Pi spine, outermost first.
    fn pi_spine(e: &Expr) -> Vec<BinderInfo> {
        let mut out = Vec::new();
        let mut cur = e;
        while let ExprKind::Pi(bd, _, body) = &**cur {
            out.push(bd.info);
            cur = body.as_ref();
        }
        out
    }

    let mut env = coind_stream_env();
    elab_in(
        &mut env,
        r"coinductive Bisim : Str → Str → Prop
| step : shd s = shd t → Bisim (stl s) (stl t) → Bisim s t",
    )
    .expect("the v1 coinductive shape must elaborate to the gfp encoding");

    use BinderInfo::{Default as E, Implicit as I};
    // (name, rendered kernel type, outer Pi-spine binder infos). The `f`/`s`
    // names below are the PRINTER'S deterministic domain-derived names, not
    // the generator's — renaming a generated binder cannot move this table,
    // but any statement-level change does.
    #[rustfmt::skip]
    let expected: &[(&str, &str, &[BinderInfo])] = &[
        ("Bisim", "Str -> Str -> Prop", &[E, E]),
        ("Bisim.F", "(Str -> Str -> Prop) -> Str -> Str -> Prop", &[E, E, E]),
        ("Bisim.coind",
         "(f : Str -> Str -> Prop) -> ((s : Str) -> (s1 : Str) -> f s s1 -> Bisim.F f s s1) \
          -> ((s : Str) -> (s1 : Str) -> f s s1 -> Bisim s s1)",
         &[E, E, E, E, E]),
        ("Bisim.F_mono",
         "(f : Str -> Str -> Prop) -> (f1 : Str -> Str -> Prop) \
          -> ((s : Str) -> (s1 : Str) -> f s s1 -> f1 s s1) \
          -> ((s : Str) -> (s1 : Str) -> Bisim.F f s s1 -> Bisim.F f1 s s1)",
         &[E, E, E, E, E, E]),
        ("Bisim.unfold",
         "(s : Str) -> (s1 : Str) -> Bisim s s1 -> Bisim.F Bisim s s1",
         &[E, E, E]),
        ("Bisim.fold",
         "(s : Str) -> (s1 : Str) -> Bisim.F Bisim s s1 -> Bisim s s1",
         &[E, E, E]),
        ("Bisim.step",
         "(s : Str) -> (s1 : Str) -> shd s = shd s1 \
          -> Bisim (stl s) (stl s1) -> Bisim s s1",
         &[I, I, E, E]),
        // PACO/ACCUMULATION RUNG (2026-08-26): two NEW companions join the
        // golden — the pinned family grows 7 -> 9. `Bisim.acc` is strong
        // coinduction (the candidate may step into the union with Bisim
        // itself); `Bisim.coind_upto` is Park up to a caller-supplied
        // compatible closure (mono/compat/idem/incl side conditions, in
        // that order).
        ("Bisim.acc",
         "(f : Str -> Str -> Prop) \
          -> ((s : Str) -> (s1 : Str) -> f s s1 \
          -> Bisim.F (fun (s2 : Str) => fun (s3 : Str) => f s2 s3 ∨ Bisim s2 s3) s s1) \
          -> ((s : Str) -> (s1 : Str) -> f s s1 -> Bisim s s1)",
         &[E, E, E, E, E]),
        ("Bisim.coind_upto",
         "(f : (Str -> Str -> Prop) -> Str -> Str -> Prop) \
          -> ((f1 : Str -> Str -> Prop) -> (f2 : Str -> Str -> Prop) -> ((s : Str) -> (s1 : Str) -> f1 s s1 -> f2 s s1) -> ((s : Str) -> (s1 : Str) -> f f1 s s1 -> f f2 s s1)) \
          -> ((f1 : Str -> Str -> Prop) -> (s : Str) -> (s1 : Str) -> f (Bisim.F f1) s s1 -> Bisim.F (f f1) s s1) \
          -> ((f1 : Str -> Str -> Prop) -> (s : Str) -> (s1 : Str) -> f (f f1) s s1 -> f f1 s s1) \
          -> ((f1 : Str -> Str -> Prop) -> (s : Str) -> (s1 : Str) -> f1 s s1 -> f f1 s s1) \
          -> ((f1 : Str -> Str -> Prop) -> ((s : Str) -> (s1 : Str) -> f1 s s1 -> Bisim.F (f f1) s s1) -> ((s : Str) -> (s1 : Str) -> f1 s s1 -> Bisim s s1))",
         &[E, E, E, E, E, E, E, E, E, E]),
        // PACO PARAMETERIZED-TOWER RUNG (measured 2026-08-26): eight NEW
        // companions join the golden — the pinned family grows 9 -> 17.
        // `Bisim.paco r` is the gfp of `fun R => Bisim.F (R ∨ r)` (union
        // order: candidate LEFT, the library's `RelUnion R r`);
        // `paco_coind`/`paco_unfold`/`paco_fold` are Park/destructor/
        // constructor at that functor; `paco_mon` is monotonicity in the
        // ACCUMULATED r; `paco_bot`/`le_paco` are the two-implication ⊥
        // correspondence (library `paco_bot_le_gfp`/`gfp_le_paco`); and
        // `paco_acc` is the faithful accumulation with the library's
        // `r ∨ r'` union (older knowledge LEFT).
        ("Bisim.paco",
         "(Str -> Str -> Prop) -> Str -> Str -> Prop",
         &[E, E, E]),
        ("Bisim.paco_coind",
         "(f : Str -> Str -> Prop) -> (f1 : Str -> Str -> Prop) \
          -> ((s : Str) -> (s1 : Str) -> f1 s s1 \
          -> Bisim.F (fun (s2 : Str) => fun (s3 : Str) => f1 s2 s3 ∨ f s2 s3) s s1) \
          -> ((s : Str) -> (s1 : Str) -> f1 s s1 -> Bisim.paco f s s1)",
         &[E, E, E, E, E, E]),
        ("Bisim.paco_unfold",
         "(f : Str -> Str -> Prop) -> (s : Str) -> (s1 : Str) -> Bisim.paco f s s1 \
          -> Bisim.F (fun (s2 : Str) => fun (s3 : Str) => Bisim.paco f s2 s3 ∨ f s2 s3) s s1",
         &[E, E, E, E]),
        ("Bisim.paco_fold",
         "(f : Str -> Str -> Prop) -> (s : Str) -> (s1 : Str) \
          -> Bisim.F (fun (s2 : Str) => fun (s3 : Str) => Bisim.paco f s2 s3 ∨ f s2 s3) s s1 \
          -> Bisim.paco f s s1",
         &[E, E, E, E]),
        ("Bisim.paco_mon",
         "(f : Str -> Str -> Prop) -> (f1 : Str -> Str -> Prop) \
          -> ((s : Str) -> (s1 : Str) -> f s s1 -> f1 s s1) \
          -> ((s : Str) -> (s1 : Str) -> Bisim.paco f s s1 -> Bisim.paco f1 s s1)",
         &[E, E, E, E, E, E]),
        ("Bisim.paco_bot",
         "(s : Str) -> (s1 : Str) \
          -> Bisim.paco (fun (s2 : Str) => fun (s3 : Str) => False) s s1 -> Bisim s s1",
         &[E, E, E]),
        ("Bisim.le_paco",
         "(f : Str -> Str -> Prop) -> (s : Str) -> (s1 : Str) -> Bisim s s1 \
          -> Bisim.paco f s s1",
         &[E, E, E, E]),
        ("Bisim.paco_acc",
         "(f : Str -> Str -> Prop) -> (f1 : Str -> Str -> Prop) \
          -> ((s : Str) -> (s1 : Str) -> f1 s s1 \
          -> Bisim.paco (fun (s2 : Str) => fun (s3 : Str) => f s2 s3 ∨ f1 s2 s3) s s1) \
          -> ((s : Str) -> (s1 : Str) -> f1 s s1 -> Bisim.paco f s s1)",
         &[E, E, E, E, E, E]),
    ];

    for (name, want_ty, want_spine) in expected {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert_eq!(
            info.type_.to_string(),
            *want_ty,
            "`{name}`: the generated statement changed"
        );
        assert_eq!(
            pi_spine(&info.type_),
            *want_spine,
            "`{name}`: the generated binder-info row changed"
        );
    }
}

/// PACO/ACCUMULATION RUNG (3a): `P.acc` in use, on a candidate too small
/// for Park. The singleton candidate `R a b := a = one ∧ b = inf` does NOT
/// close under the step — its tails are `(pred one, pred inf) ≡ (zero, inf)`,
/// which `R` does not relate — so `CoLe.coind` cannot finish with it. The
/// ACCUMULATED disjunct absorbs the tail with an already-established P-fact
/// (`CoLe.z`): exactly the fallback `P.acc` exists for. This is the test
/// that catches the drop-the-accumulated-disjunct mutation (`P.acc`
/// degenerating to Park still kernel-checks — only a consumer of the `∨ P`
/// branch can tell them apart).
///
/// MUTATION COVERAGE (measured 2026-08-26, both reverted):
/// * COHERENT weakening — `P.acc` degenerated to Park (statement's union
///   replaced by the bare candidate, proof adapted so it still
///   kernel-checks): exactly THIS test fails (`TypeMismatch` — the
///   `Or.inr` into the accumulated branch has no target) plus the golden
///   (`Bisim.acc: the generated statement changed`); all 19 other tests
///   stay green, so these two pins are the load-bearing net.
/// * INCOHERENT weakening — union dropped from the statement only, proof
///   left referencing it: every accept test fails inside the CANDIDATE-env
///   kernel check ("the generated greatest-fixpoint declaration `X.acc`
///   failed to elaborate/kernel-check … REJECTED rather than partially
///   registered") — the fail-closed net catches the generator bug before
///   anything registers.
///
/// `@CoLe.z (pred a) (pred b)` is the measured greedy-implicit workaround
/// (the `div_step_use` quirk family): the bare spelling elaborates the
/// `congrArg` premise against `?m 0 = 0` FIRST and mis-commits `?m` to the
/// congrArg lambda before the expected `CoLe (pred a) (pred b)` fixes it.
#[test]
fn test_elab_coinductive_acc_accumulated_candidate() {
    let mut env = coind_cole_env();
    elab_in(
        &mut env,
        r"theorem cole_one_inf_acc : CoLe one inf :=
  CoLe.acc (fun a b => a = one ∧ b = inf)
    (fun a b h => Or.inr (And.intro
      (congrArg (fun (q : CN) => q 0) (And.left h))
      (And.intro (congrArg (fun (q : CN) => q 0) (And.right h))
        (Or.inr (@CoLe.z (pred a) (pred b) (congrArg (fun (q : CN) => q 1) (And.left h)))))))
    one inf (And.intro rfl rfl)",
    )
    .expect("`CoLe.acc` must prove `CoLe one inf` through the accumulated disjunct");

    // ANTI-VACUITY (3b): `P.acc` with a trivially-FALSE candidate must not
    // mint a false P-fact. The step obligation is vacuously dischargeable
    // (`False.elim`), but the conclusion still demands `R v⃗` — a proof of
    // `False` — so the cheat is kernel-refused. Guards against the acc
    // statement accidentally concluding `∀ v⃗, P v⃗`.
    let mut cheat_env = coind_cole_env();
    elab_in(
        &mut cheat_env,
        r"theorem cole_acc_cheat : CoLe one zero :=
  CoLe.acc (fun a b => False) (fun a b h => False.elim h) one zero rfl",
    )
    .expect_err("`CoLe.acc` with a False candidate must not prove `CoLe one zero`");
    assert!(
        cheat_env
            .get_const(&Name::from_string("cole_acc_cheat"))
            .is_none(),
        "the refused acc cheat must not register"
    );
}

/// PACO/ACCUMULATION RUNG (3c): `P.coind_upto` in use with the canonical
/// "up to P itself" closure `clo R := R ∨ CoLe`, every side condition
/// (mono / compat / idem / incl) discharged INLINE — compat is the real
/// one: it consumes `CoLe.unfold` + `CoLe.F_mono`. Proves the same fact as
/// the acc test, pinning that `P.acc` is exactly this closure instance and
/// that the general closure interface is USABLE, not just statable.
#[test]
fn test_elab_coinductive_upto_closure_use() {
    let mut env = coind_cole_env();
    elab_in(
        &mut env,
        r"theorem cole_one_inf_upto : CoLe one inf :=
  CoLe.coind_upto (fun R => fun a b => R a b ∨ CoLe a b)
    (fun R S hle a b h => Or.elim h (fun hr => Or.inl (hle a b hr)) (fun hp => Or.inr hp))
    (fun R a b h => Or.elim h
      (fun hf => CoLe.F_mono R (fun x y => R x y ∨ CoLe x y) (fun x y hr => Or.inl hr) a b hf)
      (fun hp => CoLe.F_mono CoLe (fun x y => R x y ∨ CoLe x y) (fun x y hq => Or.inr hq) a b
        (CoLe.unfold a b hp)))
    (fun R a b h => Or.elim h (fun hi => hi) (fun hp => Or.inr hp))
    (fun R a b h => Or.inl h)
    (fun a b => a = one ∧ b = inf)
    (fun a b h => Or.inr (And.intro
      (congrArg (fun (q : CN) => q 0) (And.left h))
      (And.intro (congrArg (fun (q : CN) => q 0) (And.right h))
        (Or.inr (@CoLe.z (pred a) (pred b) (congrArg (fun (q : CN) => q 1) (And.left h)))))))
    one inf (And.intro rfl rfl)",
    )
    .expect("`CoLe.coind_upto` with the union-with-P closure must prove `CoLe one inf`");
}

/// PACO PARAMETERIZED-TOWER RUNG: the compositional use-case the tower
/// exists for — TWO accumulation levels, the classic pcofix-inside-pcofix
/// shape, over the Milner weak-bisimulation fixture. The outer
/// `WBisim.paco_acc` accumulates the candidate {(loop, loop)} at level ⊥;
/// its step (`paco_fold`) answers the loop's tau-step and routes the tail
/// NOT into its own accumulated side but into a NESTED `paco_acc` at the
/// enlarged level `⊥ ∨ r₀` — whose own step then discharges its tail by
/// citing the OUTER candidate from under BOTH accumulated unions
/// (`Or.inr (Or.inl (Or.inr …))`: s₂-side, then the outer level's union,
/// then r₀). That cross-level citation is exactly what `P.acc` (one flat
/// union with P) cannot express and the parameterized tower can. Like
/// `bisim_upto_eq_demo`/`CoLe_one_inf_acc`, the MECHANISM is the point —
/// `wbisim_refl` proves a superset directly.
///
/// ANTI-VACUITY: the tower must not mint P-facts from a False candidate —
/// `paco_acc`'s conclusion still demands `r' v⃗`, so the cheat is
/// kernel-refused and nothing registers.
///
/// MUTATION COVERAGE (measured 2026-08-26, reverted): COHERENT weakening of
/// `paco_acc`'s accumulated disjunct — the hypothesis's `paco (r ∨ r')`
/// degraded to `paco r` and the proof adapted to the identity so the
/// generated theorem still kernel-checks (the dangerous mutation: nothing
/// kernel-side objects). Exactly TWO tests fail: the golden
/// (`Bisim.paco_acc: the generated statement changed` — the union vanished
/// from the hypothesis) and THIS test (`TypeMismatch` — the nested level's
/// cross-level `Or.inr (Or.inl …)` routing has no target once the
/// accumulation level loses the union); all 28 other battery tests stay
/// green, including `paco_tower_correspondences` (it never routes through
/// the accumulated disjunct). These two pins are the load-bearing net.
#[test]
fn test_elab_coinductive_paco_two_level_accumulation() {
    let mut env = coind_lts_env();
    for src in [
        r"inductive Act
| tau : Act
| act : Act",
        r"def AStep (u : St) (x : Act) (v : St) : Prop := u = St.loop ∧ v = St.loop ∧ x = Act.tau",
    ] {
        let d = parse_decl_for_elab(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        crate::elaborate_decl_and_register(&mut env, &d)
            .unwrap_or_else(|e| panic!("elab `{src}`: {e:?}"));
    }
    elab_in(
        &mut env,
        r"coinductive WBisim : St → St → Prop
| step : (∀ (x : Act) (s2 : St), AStep s x s2 → ∃ t2, AStep t x t2 ∧ WBisim s2 t2) → (∀ (x : Act) (t2 : St), AStep t x t2 → ∃ s2, AStep s x s2 ∧ WBisim s2 t2) → WBisim s t",
    )
    .expect("the WBisim fixture must elaborate");

    elab_in(
        &mut env,
        r"theorem wbisim_loop_paco : WBisim St.loop St.loop :=
  WBisim.paco_bot St.loop St.loop
    (WBisim.paco_acc (fun a b => False) (fun a b => a = St.loop ∧ b = St.loop)
      (fun s t h =>
        WBisim.paco_fold (fun a b => False ∨ (a = St.loop ∧ b = St.loop)) s t
          (And.intro
            (fun x s2 hs => Exists.intro s2 (And.intro
              (And.intro (And.right h) (And.right hs))
              (Or.inl
                (WBisim.paco_acc (fun a b => False ∨ (a = St.loop ∧ b = St.loop))
                  (fun a b => a = St.loop ∧ b = St.loop)
                  (fun a b h2 =>
                    WBisim.paco_fold
                      (fun a b => (False ∨ (a = St.loop ∧ b = St.loop)) ∨ (a = St.loop ∧ b = St.loop))
                      a b
                      (And.intro
                        (fun x2 c hc => Exists.intro c (And.intro
                          (And.intro (And.right h2) (And.right hc))
                          (Or.inr (Or.inl (Or.inr (And.intro
                            (And.left (And.right hc)) (And.left (And.right hc))))))))
                        (fun x2 c hc => Exists.intro c (And.intro
                          (And.intro (And.left h2) (And.right hc))
                          (Or.inr (Or.inl (Or.inr (And.intro
                            (And.left (And.right hc)) (And.left (And.right hc))))))))))
                  s2 s2 (And.intro (And.left (And.right hs)) (And.left (And.right hs)))))))
            (fun x t2 ht => Exists.intro t2 (And.intro
              (And.intro (And.left h) (And.right ht))
              (Or.inr (Or.inr (And.intro
                (And.left (And.right ht)) (And.left (And.right ht)))))))))
      St.loop St.loop (And.intro rfl rfl))",
    )
    .expect("two-level paco accumulation must prove `WBisim loop loop` through the tower");

    // ANTI-VACUITY: a False candidate cannot close `paco_acc`'s conclusion
    // (`r' v⃗` is demanded at the use site), so no false P-fact is minted.
    let mut cheat_env = coind_lts_env();
    for src in [
        r"inductive Act
| tau : Act
| act : Act",
        r"def AStep (u : St) (x : Act) (v : St) : Prop := u = St.loop ∧ v = St.loop ∧ x = Act.tau",
    ] {
        let d = parse_decl_for_elab(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        crate::elaborate_decl_and_register(&mut cheat_env, &d)
            .unwrap_or_else(|e| panic!("elab `{src}`: {e:?}"));
    }
    elab_in(
        &mut cheat_env,
        r"coinductive WBisim : St → St → Prop
| step : (∀ (x : Act) (s2 : St), AStep s x s2 → ∃ t2, AStep t x t2 ∧ WBisim s2 t2) → (∀ (x : Act) (t2 : St), AStep t x t2 → ∃ s2, AStep s x s2 ∧ WBisim s2 t2) → WBisim s t",
    )
    .expect("the cheat env's WBisim fixture must elaborate");
    elab_in(
        &mut cheat_env,
        r"theorem wbisim_paco_cheat : WBisim St.loop St.stuck :=
  WBisim.paco_bot St.loop St.stuck
    (WBisim.paco_acc (fun a b => False) (fun a b => False)
      (fun a b h => False.elim h)
      St.loop St.stuck rfl)",
    )
    .expect_err("a False-candidate tower cheat must not prove `WBisim loop stuck`");
    assert!(
        cheat_env
            .get_const(&Name::from_string("wbisim_paco_cheat"))
            .is_none(),
        "the refused tower cheat must not register"
    );
}

/// PACO PARAMETERIZED-TOWER RUNG: the ⊥ correspondence and the remaining
/// tower lemmas in USE — `le_paco` injects any established P-fact into any
/// accumulation level (the library's `gfp_le_paco`), `paco_bot` brings a
/// ⊥-level tower fact back to P (the library's `paco_bot_le_gfp`; composed
/// they round-trip), `paco_mon` widens the accumulated relation, and
/// `paco_unfold`/`paco_fold` are mutually inverse-shaped (one destruct,
/// one rebuild — the pin that keeps their statements aligned).
#[test]
fn test_elab_coinductive_paco_tower_correspondences() {
    let mut env = coind_cole_env();
    elab_in(
        &mut env,
        r"theorem cole_le_paco_use : ∀ r : CN → CN → Prop, ∀ m n : CN, CoLe m n → CoLe.paco r m n :=
  fun r m n h => CoLe.le_paco r m n h",
    )
    .expect("`CoLe.le_paco` must inject an established P-fact into every paco level");
    elab_in(
        &mut env,
        r"theorem cole_paco_bot_roundtrip : ∀ m n : CN, CoLe m n → CoLe m n :=
  fun m n h => CoLe.paco_bot m n (CoLe.le_paco (fun a b => False) m n h)",
    )
    .expect("the two-implication ⊥ correspondence must round-trip through the tower");
    elab_in(
        &mut env,
        r"theorem cole_paco_mon_use : ∀ m n : CN,
    CoLe.paco (fun a b => False) m n → CoLe.paco (fun a b => a = b) m n :=
  fun m n h => CoLe.paco_mon (fun a b => False) (fun a b => a = b)
    (fun a b hf => False.elim hf) m n h",
    )
    .expect("`CoLe.paco_mon` must widen the accumulated relation");
    elab_in(
        &mut env,
        r"theorem cole_paco_unfold_fold : ∀ r : CN → CN → Prop, ∀ m n : CN,
    CoLe.paco r m n → CoLe.paco r m n :=
  fun r m n h => CoLe.paco_fold r m n (CoLe.paco_unfold r m n h)",
    )
    .expect("`CoLe.paco_unfold`/`CoLe.paco_fold` must be mutually inverse-shaped");
}

/// A rejected `coinductive` must leave NOTHING behind: no half-built
/// companion family in the environment — including the Brick 1 `.cases`
/// inversion companion. The fixture's FIRST constructor is in-envelope, so
/// this also pins that a bad LATER constructor rejects the whole family.
#[test]
fn test_elab_coinductive_reject_registers_nothing() {
    let mut env = coind_stream_env();
    let err = elab_in(
        &mut env,
        r"coinductive Two : Str → Str → Prop
| l : Two (stl s) t → Two s t
| r : Two s (stl t) → Two (stl s) t",
    )
    .expect_err("a compound-target constructor must reject the declaration");
    assert!(matches!(err, ElabError::Unsupported { .. }), "{err:?}");
    for name in [
        "Two",
        "Two.F",
        "Two.coind",
        "Two.F_mono",
        "Two.unfold",
        "Two.fold",
        "Two.l",
        "Two.r",
        "Two.cases",
        "Two.acc",
        "Two.coind_upto",
        "Two.paco",
        "Two.paco_coind",
        "Two.paco_unfold",
        "Two.paco_fold",
        "Two.paco_mon",
        "Two.paco_bot",
        "Two.le_paco",
        "Two.paco_acc",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` must not survive a rejected coinductive declaration"
        );
    }
}

/// BRICK 1 (3a): the two-constructor `Two` — the exact declaration the v1
/// reject battery pinned — now ACCEPTS through the disjunctive lowering,
/// with the full companion family (per-constructor intros + `.cases`)
/// registered, kernel-checked and axiom-free.
#[test]
fn test_elab_coinductive_multi_ctor_accepts() {
    let mut env = coind_stream_env();
    elab_in(
        &mut env,
        r"coinductive Two : Str → Str → Prop
| l : Two (stl s) t → Two s t
| r : Two s (stl t) → Two s t",
    )
    .expect("a two-constructor v1-shaped coinductive must elaborate (Brick 1)");
    for name in [
        "Two",
        "Two.F",
        "Two.coind",
        "Two.F_mono",
        "Two.unfold",
        "Two.fold",
        "Two.l",
        "Two.r",
        "Two.cases",
        "Two.acc",
        "Two.coind_upto",
        "Two.paco",
        "Two.paco_coind",
        "Two.paco_unfold",
        "Two.paco_fold",
        "Two.paco_mon",
        "Two.paco_bot",
        "Two.le_paco",
        "Two.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("Two.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );
}

/// Prelude env plus a conat model on `CN := Nat → Nat` (head bit at 0,
/// `pred` shifts): `inf` is all-1s, `zero` all-0s, `one` is 1 then 0s.
/// First-order carriers on purpose — `funext` is not in the builtin prelude,
/// so every test equation lives at `Nat` heads probed by application.
fn coind_conat_env() -> Environment {
    let mut env = Environment::with_prelude();
    for src in [
        r"def CN : Type := Nat → Nat",
        r"def pred (m : CN) : CN := fun n => m (Nat.succ n)",
        r"def inf : CN := fun k => 1",
        r"def zero : CN := fun k => 0",
        r"def one : CN := fun k => match k with | Nat.zero => 1 | Nat.succ j => 0",
    ] {
        let d = parse_decl_for_elab(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        crate::elaborate_decl_and_register(&mut env, &d)
            .unwrap_or_else(|e| panic!("elab `{src}`: {e:?}"));
    }
    env
}

/// The conat env plus the K = 2 `CoLe` comparison. Constructor `s`
/// deliberately names its targets `a b` (vs `z`'s `m n`), so the α-rename
/// onto the shared index row runs in this mainline accept path.
fn coind_cole_env() -> Environment {
    let mut env = coind_conat_env();
    elab_in(
        &mut env,
        r"coinductive CoLe : CN → CN → Prop
| z : m 0 = 0 → CoLe m n
| s : a 0 = 1 → b 0 = 1 → CoLe (pred a) (pred b) → CoLe a b",
    )
    .expect("the two-constructor CoLe must elaborate through the disjunctive lowering");
    env
}

/// BRICK 1 (3b): the K = 2 gfp discriminator. `CoLe inf inf` has NO finite
/// derivation — arm `z` never applies to `inf` (its head is 1), and arm `s`
/// recurses on `(pred inf, pred inf) ≡ (inf, inf)` forever — so the LEAST
/// fixpoint of this functor does not relate `inf` to itself. It is provable
/// exactly because `CoLe` is the GREATEST fixpoint: Park coinduction with
/// the candidate `R a b := a = inf ∧ b = inf` lands in the SECOND disjunct.
#[test]
fn test_elab_coinductive_two_ctor_gfp_discriminator() {
    let mut env = coind_cole_env();
    for name in [
        "CoLe",
        "CoLe.F",
        "CoLe.coind",
        "CoLe.F_mono",
        "CoLe.unfold",
        "CoLe.fold",
        "CoLe.z",
        "CoLe.s",
        "CoLe.cases",
        "CoLe.acc",
        "CoLe.coind_upto",
        "CoLe.paco",
        "CoLe.paco_coind",
        "CoLe.paco_unfold",
        "CoLe.paco_fold",
        "CoLe.paco_mon",
        "CoLe.paco_bot",
        "CoLe.le_paco",
        "CoLe.paco_acc",
    ] {
        let n = Name::from_string(name);
        assert!(env.get_const(&n).is_some(), "`{name}` must be registered");
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("CoLe.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // The first intro at its declared type (`zero`'s head is 0).
    elab_in(
        &mut env,
        r"theorem cole_zero_inf : CoLe zero inf := CoLe.z rfl",
    )
    .expect("the first intro must prove `CoLe zero inf`");

    // THE discriminator.
    elab_in(
        &mut env,
        r"theorem cole_inf_inf : CoLe inf inf :=
  CoLe.coind (fun a b => a = inf ∧ b = inf)
    (fun a b h => Or.inr (And.intro (congrArg (fun (q : CN) => q 0) (And.left h))
      (And.intro (congrArg (fun (q : CN) => q 0) (And.right h))
        (And.intro (congrArg pred (And.left h)) (congrArg pred (And.right h))))))
    inf inf (And.intro rfl rfl)",
    )
    .expect("Park coinduction through `CoLe.coind` must prove `CoLe inf inf`");
}

/// BRICK 1 (3c): inversion refutation. `CoLe one zero → False` is
/// impossible without the `cases` principle: only the case split exposes
/// that EVERY arm contradicts a head computation (`one 0` is 1, so arm `z`
/// yields `1 = 0`; `zero 0` is 0, so arm `s` yields `0 = 1`).
#[test]
fn test_elab_coinductive_cases_inversion_refutes() {
    let mut env = coind_cole_env();
    elab_in(
        &mut env,
        r"theorem cole_one_zero_false : CoLe one zero → False :=
  fun h => CoLe.cases h False
    (fun h1 => Nat.noConfusion h1)
    (fun h1 h2 h3 => Nat.noConfusion h2)",
    )
    .expect("`CoLe.cases` must refute `CoLe one zero`");
}

/// BRICK 1 (3d): arm-selection round trip. `n 0 = 1` is recoverable ONLY
/// from arm 2 (arm 1 is absurd under `m 0 = 1`), and the witness is BUILT
/// with the second intro. The m-vs-n asymmetry keeps two mutations live:
/// swapped `Or` injections fail the declaration's own kernel check, and a
/// reversed α-rename direction elaborates the declaration but fails HERE
/// (arm 2 would hand back `m 0 = 1` where `n 0 = 1` is required).
#[test]
fn test_elab_coinductive_arm_selection_round_trip() {
    let mut env = coind_cole_env();
    elab_in(
        &mut env,
        r"theorem cole_pos_inv : ∀ m n : CN, CoLe m n → m 0 = 1 → n 0 = 1 :=
  fun m n p h1 => CoLe.cases p (n 0 = 1)
    (fun hz => Nat.noConfusion (Eq.trans (Eq.symm h1) hz))
    (fun h1s h2 h3 => h2)",
    )
    .expect("head inversion through arm 2 of `CoLe.cases` must elaborate");
    elab_in(
        &mut env,
        r"theorem inf_head_one : inf 0 = 1 :=
  cole_pos_inv one inf (CoLe.s rfl rfl (CoLe.z rfl)) rfl",
    )
    .expect("the second intro must round-trip through the second cases arm");
}

/// Prelude env plus a first-order LTS: two states and a step relation with
/// a single edge `loop → loop` (`stuck` has no successor). `Step` is a
/// `def` on purpose — its unfolding makes the no-step lemma a computation
/// (`St.noConfusion` on the head equality), no inductive inversion needed.
fn coind_lts_env() -> Environment {
    let mut env = Environment::with_prelude();
    for src in [
        r"inductive St
| loop : St
| stuck : St",
        r"def Step (a b : St) : Prop := a = St.loop ∧ b = St.loop",
    ] {
        let d = parse_decl_for_elab(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        crate::elaborate_decl_and_register(&mut env, &d)
            .unwrap_or_else(|e| panic!("elab `{src}`: {e:?}"));
    }
    env
}

/// BRICK 2 (3a) FLAGSHIP: a constructor with a LEADING explicitly-typed
/// binder — `| step (q : St) : Step p q → Divg q → Divg p` — lowers to the
/// `∃ q` functor disjunct. `Divg loop` is THE gfp discriminator (every
/// least-fixpoint derivation would need an infinite `Step` chain), and
/// `Divg stuck → False` consumes the ∃-witness in the `cases` arm.
#[test]
fn test_elab_coinductive_exists_binder_flagship() {
    use clean_kernel::{BinderInfo, Expr, ExprKind};

    let mut env = coind_lts_env();
    elab_in(
        &mut env,
        r"coinductive Divg : St → Prop
| step (q : St) : Step p q → Divg q → Divg p",
    )
    .expect("a leading-binder constructor must elaborate through the ∃ lowering (Brick 2)");

    for name in [
        "Divg",
        "Divg.F",
        "Divg.coind",
        "Divg.F_mono",
        "Divg.unfold",
        "Divg.fold",
        "Divg.step",
        "Divg.cases",
        "Divg.acc",
        "Divg.coind_upto",
        "Divg.paco",
        "Divg.paco_coind",
        "Divg.paco_unfold",
        "Divg.paco_fold",
        "Divg.paco_mon",
        "Divg.paco_bot",
        "Divg.le_paco",
        "Divg.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("Divg.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // The intro statement pins Brick 2's binder placement: the index stays
    // IMPLICIT, the declared binder leads as an EXPLICIT ∀ before the
    // premises.
    fn pi_spine(e: &Expr) -> Vec<BinderInfo> {
        let mut out = Vec::new();
        let mut cur = e;
        while let ExprKind::Pi(bd, _, body) = &**cur {
            out.push(bd.info);
            cur = body.as_ref();
        }
        out
    }
    let step_ty = &env
        .get_const(&Name::from_string("Divg.step"))
        .expect("Divg.step must be registered")
        .type_;
    use BinderInfo::{Default as E, Implicit as I};
    assert_eq!(
        pi_spine(step_ty),
        vec![I, E, E, E],
        "`Divg.step` must keep the index implicit and lead with the \
         explicit declared binder: {step_ty}"
    );

    // THE discriminator: Park coinduction with the candidate
    // `R s := s = loop` — the witness `q := loop` discharges the ∃. The
    // ascription spells the post-fixpoint target in its unfolded ∃-form:
    // checking a bare `Exists.intro` against the still-folded `Divg.F R s`
    // trips the elaborator's higher-order `?p witness` handling (the meta
    // gets committed before the functor is unfolded) — a pre-existing
    // unifier limitation this brick surfaces, not a lowering defect; the
    // ascribed form is defeq and elaborates first-order.
    elab_in(
        &mut env,
        r"theorem div_loop : Divg St.loop :=
  Divg.coind (fun s => s = St.loop)
    (fun s h => (Exists.intro St.loop (And.intro (And.intro h rfl) rfl)
      : ∃ q : St, Step s q ∧ q = St.loop))
    St.loop rfl",
    )
    .expect("Park coinduction through `Divg.coind` must prove `Divg St.loop`");

    // The declared constructor is usable at its declared type, the binder
    // supplied first. `@`-explicit on purpose: the bare `Divg.step q h1 h2`
    // trips a pre-existing elaborator quirk (an explicit argument whose
    // type matches the implicit index domain is greedily consumed by the
    // implicit slot) — measured, reported, not this brick's lane.
    elab_in(
        &mut env,
        r"theorem div_step_use : ∀ p : St, ∀ q : St, Step p q → Divg q → Divg p :=
  fun p q h1 h2 => @Divg.step p q h1 h2",
    )
    .expect("the generated constructor must take the declared binder as its leading argument");

    // Inversion refutation: the arm receives the ∃-witness `q` and the
    // step out of `stuck`, which contradicts by computation.
    elab_in(
        &mut env,
        r"theorem div_stuck_false : Divg St.stuck → False :=
  fun h => Divg.cases h False (fun q hs hd => St.noConfusion (And.left hs))",
    )
    .expect("`Divg.cases` must hand the arm the ∃-witness and refute `Divg St.stuck`");
}

/// BRICK 2: a TWO-binder constructor pins the ∃ nest ORDER end to end
/// (declaration order, outermost first). This is the fixture that catches
/// the reorder mutation: with `∃ r, ∃ q` in the functor but `Exists.intro
/// q (Exists.intro r …)` in the intro, the asymmetric `Step p q ∧ Step q r`
/// conjunction fails the candidate kernel check.
#[test]
fn test_elab_coinductive_two_binder_chain() {
    let mut env = coind_lts_env();
    elab_in(
        &mut env,
        r"coinductive Div2 : St → Prop
| step (q : St) (r : St) : Step p q → Step q r → Div2 r → Div2 p",
    )
    .expect("a two-binder constructor must elaborate through the nested ∃ lowering");

    // Park coinduction supplies BOTH witnesses in declaration order. The
    // anonymous constructor is the robust ∃-introduction spelling here —
    // it elaborates expected-type-first, where a bare nested
    // `Exists.intro` chain trips the higher-order `?p witness` unifier
    // limitation documented on `div_loop`.
    elab_in(
        &mut env,
        r"theorem div2_loop : Div2 St.loop :=
  Div2.coind (fun s => s = St.loop)
    (fun s h => ⟨St.loop, St.loop,
      And.intro (And.intro h rfl) (And.intro (And.intro rfl rfl) rfl)⟩)
    St.loop rfl",
    )
    .expect("Park coinduction must prove `Div2 St.loop` through the two-witness disjunct");

    // The intro takes the binders first, in declaration order
    // (`@`-explicit for the same greedy-implicit quirk as `div_step_use`).
    elab_in(
        &mut env,
        r"theorem div2_step_use : ∀ p : St, ∀ q : St, ∀ r : St,
    Step p q → Step q r → Div2 r → Div2 p :=
  fun p q r h1 h2 h3 => @Div2.step p q r h1 h2 h3",
    )
    .expect("the two-binder intro must take both declared binders in order");

    // The cases arm receives both witnesses then the premises.
    elab_in(
        &mut env,
        r"theorem div2_stuck_false : Div2 St.stuck → False :=
  fun h => Div2.cases h False (fun q r h1 h2 h3 => St.noConfusion (And.left h1))",
    )
    .expect("`Div2.cases` must hand the arm both ∃-witnesses");
}

/// BRICK 2 × BRICK 1: a binder-carrying disjunct UNDER an `Or` layer — one
/// binder-free constructor plus one with an ∃ — exercises the
/// `Exists.elim`/`Exists.intro` plumbing inside the `Or.elim` cascade of
/// `F_mono` (declaration kernel check) and `cases` (the dichotomy below).
#[test]
fn test_elab_coinductive_exists_binder_under_or() {
    let mut env = coind_lts_env();
    elab_in(
        &mut env,
        r"coinductive CoRun : St → Prop
| halt : p = St.stuck → CoRun p
| run (q : St) : Step p q → CoRun q → CoRun p",
    )
    .expect("a mixed binder/binder-free two-constructor coinductive must elaborate");

    // First disjunct: plain intro.
    elab_in(
        &mut env,
        r"theorem corun_stuck : CoRun St.stuck := CoRun.halt rfl",
    )
    .expect("the binder-free intro must still work beside a binder-carrying one");

    // Second disjunct: Park lands the candidate under `Or.inr` + ∃.
    elab_in(
        &mut env,
        r"theorem corun_loop : CoRun St.loop :=
  CoRun.coind (fun s => s = St.loop)
    (fun s h => Or.inr (Exists.intro St.loop (And.intro (And.intro h rfl) rfl)))
    St.loop rfl",
    )
    .expect("Park coinduction must prove `CoRun St.loop` through the ∃ disjunct under Or");

    // The dichotomy consumes the ∃-witness inside the SECOND cases arm.
    elab_in(
        &mut env,
        r"theorem corun_dichotomy : ∀ p : St, CoRun p → p = St.stuck ∨ p = St.loop :=
  fun p hc => CoRun.cases hc (p = St.stuck ∨ p = St.loop)
    (fun he => Or.inl he)
    (fun q h1 h2 => Or.inr (And.left h1))",
    )
    .expect("`CoRun.cases` must destructure the ∃ only in the binder-carrying arm");
}

/// BRICK 3 (3a): CONSTANT targets. `Cycle 0`/`Cycle 1` have no bare target
/// variable at all — every position is an index equation and the whole row
/// is generated. `Cycle 0` is the gfp discriminator (its only derivations
/// are infinite: a→b→a→…), and `Cycle 2 → False` needs the equations in the
/// `cases` arms: only they record which index each constructor concludes
/// at, and `Nat` discrimination refutes both.
#[test]
fn test_elab_coinductive_constant_target_cycle() {
    let mut env = Environment::with_prelude();
    elab_in(
        &mut env,
        r"coinductive Cycle : Nat → Prop
| a : Cycle 1 → Cycle 0
| b : Cycle 0 → Cycle 1",
    )
    .expect("constant-target constructors must elaborate through the index-equation lowering");

    for name in [
        "Cycle",
        "Cycle.F",
        "Cycle.coind",
        "Cycle.F_mono",
        "Cycle.unfold",
        "Cycle.fold",
        "Cycle.a",
        "Cycle.b",
        "Cycle.cases",
        "Cycle.acc",
        "Cycle.coind_upto",
        "Cycle.paco",
        "Cycle.paco_coind",
        "Cycle.paco_unfold",
        "Cycle.paco_fold",
        "Cycle.paco_mon",
        "Cycle.paco_bot",
        "Cycle.le_paco",
        "Cycle.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("Cycle.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // THE discriminator: Park coinduction on `R n := n = 0 ∨ n = 1`. Each
    // case lands in ITS OWN disjunct and closes the index equation with
    // symmetry — the written-target-on-the-left orientation is what makes
    // `Eq.symm h0 : 0 = n` the right shape.
    elab_in(
        &mut env,
        r"theorem cycle_zero : Cycle 0 :=
  Cycle.coind (fun n => n = 0 ∨ n = 1)
    (fun n h => Or.elim h
      (fun h0 => Or.inl (And.intro (Eq.symm h0) (Or.inr rfl)))
      (fun h1 => Or.inr (And.intro (Eq.symm h1) (Or.inl rfl))))
    0 (Or.inl rfl)",
    )
    .expect("Park coinduction through `Cycle.coind` must prove `Cycle 0`");

    // The intros conclude at the WRITTEN constant indices — no implicit
    // index header, no explicit binders: `Cycle.b : Cycle 0 → Cycle 1`.
    elab_in(
        &mut env,
        r"theorem cycle_one : Cycle 1 := Cycle.b cycle_zero",
    )
    .expect("the equation-target intro must conclude at its written index");

    // Inversion refutation: arm `a` receives `0 = 2`, arm `b` receives
    // `1 = 2`; `Nat.noConfusion` discriminates the first outright and
    // yields succ-injectivity (`0 = 1`, discriminated again) on the second.
    elab_in(
        &mut env,
        r"theorem cycle_two_false : Cycle 2 → False :=
  fun h => Cycle.cases h False
    (fun e1 hr => Nat.noConfusion e1)
    (fun e1 hr => Nat.noConfusion e1 (fun e0 => Nat.noConfusion e0))",
    )
    .expect("`Cycle.cases` + Nat discrimination must refute `Cycle 2`");
}

/// BRICK 3 (3b): a COMPOUND target over a declared binder. `InfDesc`'s only
/// rule concludes at `Nat.succ k`, so the functor disjunct is
/// `∃ k, Nat.succ k = v ∧ R k` — and `InfDesc 0 → False` falls to
/// `noConfusion` on the arm's `Nat.succ k = 0` equation hypothesis.
#[test]
fn test_elab_coinductive_compound_target_infdesc() {
    let mut env = Environment::with_prelude();
    elab_in(
        &mut env,
        r"coinductive InfDesc : Nat → Prop
| step (k : Nat) : InfDesc k → InfDesc (Nat.succ k)",
    )
    .expect("a compound target over a declared binder must elaborate (Brick 3)");

    for name in [
        "InfDesc",
        "InfDesc.F",
        "InfDesc.coind",
        "InfDesc.F_mono",
        "InfDesc.unfold",
        "InfDesc.fold",
        "InfDesc.step",
        "InfDesc.cases",
        "InfDesc.acc",
        "InfDesc.coind_upto",
        "InfDesc.paco",
        "InfDesc.paco_coind",
        "InfDesc.paco_unfold",
        "InfDesc.paco_fold",
        "InfDesc.paco_mon",
        "InfDesc.paco_bot",
        "InfDesc.le_paco",
        "InfDesc.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("InfDesc.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // The intro concludes at the WRITTEN target, the binder leading as an
    // explicit ∀ — usable exactly as declared.
    elab_in(
        &mut env,
        r"theorem infdesc_step_use : ∀ k : Nat, InfDesc k → InfDesc (Nat.succ k) :=
  fun k h => InfDesc.step k h",
    )
    .expect("the compound-target intro must have the declared constructor type");

    // The refutation THE brick exists for: the equation hypothesis
    // `Nat.succ k = 0` in the cases arm is discriminated by `noConfusion`.
    elab_in(
        &mut env,
        r"theorem infdesc_zero_false : InfDesc 0 → False :=
  fun h => InfDesc.cases h False (fun k he hd => Nat.noConfusion he)",
    )
    .expect("`InfDesc.cases` must hand the arm `Nat.succ k = 0` for discrimination");
}

/// BRICK 3 (3c): the equation ORIENTATION pin, statement-level. The arm of
/// `InfDesc.cases` is restated verbatim with `Nat.succ k = v` — the
/// written target on the LEFT. A generator flipping the orientation mints
/// `v = Nat.succ k`, a DIFFERENT type, and this theorem stops elaborating
/// (`Eq` is not symmetric as a type). The rendered kernel type is pinned
/// too, so the flip cannot hide behind the unifier.
///
/// MUTATION COVERAGE (measured 2026-08-26, both reverted):
/// * flipping `IndexEquation::prop` fails exactly THIS test (arm
///   restatement `TypeMismatch`), `constant_target_cycle` (the Park
///   proof's `Eq.symm h0 : 0 = n` lands on the wrong side) and
///   `repeated_var_target_diag` (fvar mismatch) — the intro `Eq.refl`s
///   and the `noConfusion` refutations SURVIVE a flip (reflexive /
///   symmetric consumers), so the statement-level pins are load-bearing;
/// * dropping the intro's `Eq.refl` conjuncts fails all six Brick-3
///   accept tests inside the CANDIDATE-env kernel check ("the generated
///   greatest-fixpoint declaration … failed to elaborate/kernel-check …
///   REJECTED rather than partially registered") — the fail-closed net
///   catches the generator bug before anything registers.
#[test]
fn test_elab_coinductive_equation_orientation_pin() {
    let mut env = Environment::with_prelude();
    elab_in(
        &mut env,
        r"coinductive InfDesc : Nat → Prop
| step (k : Nat) : InfDesc k → InfDesc (Nat.succ k)",
    )
    .expect("the InfDesc fixture must elaborate");

    elab_in(
        &mut env,
        r"theorem infdesc_arm_pin : ∀ v : Nat, InfDesc v → ∀ C : Prop,
    (∀ k : Nat, Nat.succ k = v → InfDesc k → C) → C :=
  fun v h C arm => InfDesc.cases h C arm",
    )
    .expect("the cases arm must expose `Nat.succ k = v` — written target on the LEFT");

    let cases_ty = env
        .get_const(&Name::from_string("InfDesc.cases"))
        .expect("InfDesc.cases must be registered")
        .type_
        .to_string();
    // `Display for Expr` renders `Eq` infix since 6d1663115: the LEFT
    // orientation now reads `Nat.succ n1 = n` (target on the left), not the
    // old prefix `Eq {1} Nat (Nat.succ …)` spelling.
    assert!(
        cases_ty.contains("Nat.succ n1 = n"),
        "the arm equation must spell the written target on the LEFT: {cases_ty}"
    );
}

/// BRICK 3 (3d): an EQUATIONS-ONLY constructor is now legal — `nil` has no
/// premises, its disjunct is the equations conjunction, and `CB.nil`
/// proves `CB 0 0` outright (the intro closes both equations with
/// `Eq.refl`). The no-equations-no-premises degenerate stays refused (see
/// the `CBV` battery entry).
#[test]
fn test_elab_coinductive_equations_only_ctor() {
    let mut env = Environment::with_prelude();
    elab_in(
        &mut env,
        r"coinductive CB : Nat → Nat → Prop
| nil : CB 0 0
| step (j : Nat) (k : Nat) : CB j k → CB (Nat.succ j) (Nat.succ k)",
    )
    .expect("an equations-only constructor must elaborate (Brick 3 vacuity rule)");

    for name in [
        "CB",
        "CB.F",
        "CB.nil",
        "CB.step",
        "CB.cases",
        "CB.acc",
        "CB.coind_upto",
        "CB.paco",
        "CB.paco_coind",
        "CB.paco_unfold",
        "CB.paco_fold",
        "CB.paco_mon",
        "CB.paco_bot",
        "CB.le_paco",
        "CB.paco_acc",
    ] {
        let n = Name::from_string(name);
        assert!(env.get_const(&n).is_some(), "`{name}` must be registered");
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }

    // The premise-less intro is a closed proof of its written indices.
    elab_in(&mut env, r"theorem cb_zero : CB 0 0 := CB.nil")
        .expect("the equations-only intro must prove `CB 0 0` outright");
    elab_in(&mut env, r"theorem cb_one : CB 1 1 := CB.step 0 0 CB.nil")
        .expect("the two-equation compound intro must build `CB 1 1`");

    // Refutation off the SECOND equation of each arm: `nil` yields
    // `0 = 1` (first equation), `step` yields `Nat.succ k = 0`.
    elab_in(
        &mut env,
        r"theorem cb_one_zero_false : CB 1 0 → False :=
  fun h => CB.cases h False
    (fun e1 e2 => Nat.noConfusion e1)
    (fun j k e1 e2 hr => Nat.noConfusion e2)",
    )
    .expect("`CB.cases` must hand both equation hypotheses to each arm in order");
}

/// BRICK 3: REPEATED target variables — the documented ADMIT decision. In
/// `Diag s s` the first bare occurrence substitutes (binds the index) and
/// the second carries the equation `s = v₂`, so `Diag` genuinely means
/// index equality plus the coinductive step — pinned by BOTH directions:
/// Park proves `Diag s s`, and `cases` recovers `a = b` from `Diag a b`.
/// The exact fixture sat in the v1 reject battery under "DISTINCT variable
/// arguments".
#[test]
fn test_elab_coinductive_repeated_var_target_diag() {
    let mut env = coind_stream_env();
    elab_in(
        &mut env,
        r"coinductive Diag : Str → Str → Prop
| step : Diag (stl s) (stl s) → Diag s s",
    )
    .expect("a repeated-variable target must elaborate via first-substitutes-later-equate");

    elab_in(
        &mut env,
        r"theorem diag_refl : ∀ s : Str, Diag s s :=
  fun s => Diag.coind (fun a b => a = b)
    (fun a b h => And.intro h rfl)
    s s rfl",
    )
    .expect("Park coinduction must prove `Diag s s`");

    elab_in(
        &mut env,
        r"theorem diag_eq : ∀ a b : Str, Diag a b → a = b :=
  fun a b h => Diag.cases h (a = b) (fun he hd => he)",
    )
    .expect("`Diag.cases` must expose the repeated-variable equation as real content");
}

/// BRICK 3: a bare once-occurring DECLARED BINDER in a target position is
/// index-SUBSTITUTED (no ∃, no equation) — the minimization the Brick-2
/// overlap refusal deferred. This is the EXACT `Ovl` fixture from the old
/// reject battery; its functor now comes out identical to v1 `Bisim`'s.
/// The intro keeps the DECLARED explicit binder (leading ∀) while the
/// fresh index row stays implicit — pinned by the binder-info spine.
#[test]
fn test_elab_coinductive_binder_substitution_target() {
    use clean_kernel::{BinderInfo, Expr, ExprKind};

    let mut env = coind_stream_env();
    elab_in(
        &mut env,
        r"coinductive Ovl : Str → Str → Prop
| step (s : Str) : shd s = shd t → Ovl (stl s) (stl t) → Ovl s t",
    )
    .expect("a substituted declared binder in the target must elaborate (Brick 3)");

    fn pi_spine(e: &Expr) -> Vec<BinderInfo> {
        let mut out = Vec::new();
        let mut cur = e;
        while let ExprKind::Pi(bd, _, body) = &**cur {
            out.push(bd.info);
            cur = body.as_ref();
        }
        out
    }
    let step_ty = &env
        .get_const(&Name::from_string("Ovl.step"))
        .expect("Ovl.step must be registered")
        .type_;
    use BinderInfo::{Default as E, Implicit as I};
    assert_eq!(
        pi_spine(step_ty),
        vec![I, E, E, E],
        "`Ovl.step` must bind the fresh row implicitly and keep the \
         DECLARED binder explicit: {step_ty}"
    );

    // Usable at the declared type (`@`-explicit for the same greedy-implicit
    // elaborator quirk documented on `div_step_use`; the implicit fresh row
    // `t` comes first).
    elab_in(
        &mut env,
        r"theorem ovl_use : ∀ a b : Str, shd a = shd b → Ovl (stl a) (stl b) → Ovl a b :=
  fun a b h1 h2 => @Ovl.step b a h1 h2",
    )
    .expect("the substituted-binder intro must be usable at the declared constructor type");
}

/// BRICK 3: the `Bad` battery shape WITH the binder declared — a compound
/// target over an ∃-bound variable beside a substituted fresh index. The
/// old "DISTINCT variable arguments" refusal lifted to exactly this accept.
#[test]
fn test_elab_coinductive_compound_target_with_declared_binder() {
    let mut env = coind_stream_env();
    elab_in(
        &mut env,
        r"coinductive Chase : Str → Str → Prop
| step (s : Str) : Chase s t → Chase (stl s) t",
    )
    .expect("a compound target over a DECLARED binder must elaborate (Brick 3)");

    // Intro: `{t} → ∀ (s : Str), Chase s t → Chase (stl s) t`.
    elab_in(
        &mut env,
        r"theorem chase_use : ∀ a b : Str, Chase a b → Chase (stl a) b :=
  fun a b h => @Chase.step b a h",
    )
    .expect("the compound-target intro must conclude at the written target");
}

/// GUARDED PREMISES ("P under ∀/→", the rung after Brick 4): the ∃-free
/// simulation variant — `| step : (∀ (q : St), Step s q → Sim q t) → Sim s t`
/// — the predicate under a `∀`/`→` guard, strictly positive in the
/// conclusion atom. Pins the full companion family, the Park run through
/// the guarded functor, `.unfold`/`.cases` handing back the guarded clause
/// at `P`, and the intro at its declared type.
#[test]
fn test_elab_coinductive_guarded_premise_sim() {
    let mut env = coind_lts_env();
    elab_in(
        &mut env,
        r"coinductive Sim : St → St → Prop
| step : (∀ (q : St), Step s q → Sim q t) → Sim s t",
    )
    .expect("a guarded rec-conclusion premise must elaborate (P under ∀/→)");

    for name in [
        "Sim",
        "Sim.F",
        "Sim.coind",
        "Sim.F_mono",
        "Sim.unfold",
        "Sim.fold",
        "Sim.step",
        "Sim.cases",
        "Sim.acc",
        "Sim.coind_upto",
        "Sim.paco",
        "Sim.paco_coind",
        "Sim.paco_unfold",
        "Sim.paco_fold",
        "Sim.paco_mon",
        "Sim.paco_bot",
        "Sim.le_paco",
        "Sim.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("Sim.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // THE discriminator: the least fixpoint of this functor contains only
    // pairs whose left state has no infinite `Step` chain — `(loop, t)` is
    // NOT among them — so `Sim loop loop` is provable exactly because the
    // guard sits inside a GREATEST fixpoint. The candidate constrains only
    // the right state; the guard's conclusion lands on it verbatim.
    elab_in(
        &mut env,
        r"theorem sim_loop : Sim St.loop St.loop :=
  Sim.coind (fun a b => b = St.loop)
    (fun a b h => fun q hq => h)
    St.loop St.loop rfl",
    )
    .expect("Park coinduction through the guarded functor must prove `Sim St.loop St.loop`");

    // `.unfold` hands back the guarded clause AT `Sim` itself.
    elab_in(
        &mut env,
        r"theorem sim_unfold_use : ∀ a b : St, Sim a b → ∀ q : St, Step a q → Sim q b :=
  fun a b h => Sim.unfold a b h",
    )
    .expect("`Sim.unfold` must expose the guarded clause at `Sim`");

    // The `.cases` arm receives the guarded clause whole.
    elab_in(
        &mut env,
        r"theorem sim_cases_use : ∀ a b : St, Sim a b → ∀ q : St, Step a q → Sim q b :=
  fun a b h => Sim.cases h (∀ q : St, Step a q → Sim q b) (fun g => g)",
    )
    .expect("`Sim.cases` must hand the arm the guarded clause at `Sim`");

    // The intro at its declared type: the hypothesis IS the guarded clause.
    elab_in(
        &mut env,
        r"theorem sim_step_use : ∀ a b : St, (∀ q : St, Step a q → Sim q b) → Sim a b :=
  fun a b g => Sim.step g",
    )
    .expect("the generated constructor must take the full guarded clause");
}

/// GUARDED PREMISES with an ∃-CONCLUSION — the full Milner weak-bisimulation
/// clause shape, `∀ x s', Step s x s' → ∃ t', Step t x t' ∧ P s' t'`. The
/// ∃-conclusion is IN the envelope (∃ is a positive former; `F_mono`
/// re-nests with the same witnesses). Pins the flagship WBisim declaration,
/// a Park reflexivity proof, and a `.cases` refutation that APPLIES the
/// guarded clause received by the arm.
#[test]
fn test_elab_coinductive_guarded_exists_wbisim() {
    let mut env = coind_lts_env();
    for src in [
        r"inductive Act
| tau : Act
| act : Act",
        r"def AStep (u : St) (x : Act) (v : St) : Prop := u = St.loop ∧ v = St.loop ∧ x = Act.tau",
    ] {
        let d = parse_decl_for_elab(src).unwrap_or_else(|e| panic!("parse `{src}`: {e:?}"));
        crate::elaborate_decl_and_register(&mut env, &d)
            .unwrap_or_else(|e| panic!("elab `{src}`: {e:?}"));
    }
    elab_in(
        &mut env,
        r"coinductive WBisim : St → St → Prop
| step : (∀ (x : Act) (s2 : St), AStep s x s2 → ∃ t2, AStep t x t2 ∧ WBisim s2 t2) → (∀ (x : Act) (t2 : St), AStep t x t2 → ∃ s2, AStep s x s2 ∧ WBisim s2 t2) → WBisim s t",
    )
    .expect("the weak-bisimulation clause shape must elaborate (∃-conclusion under a guard)");

    for name in [
        "WBisim",
        "WBisim.F",
        "WBisim.coind",
        "WBisim.F_mono",
        "WBisim.unfold",
        "WBisim.fold",
        "WBisim.step",
        "WBisim.cases",
        "WBisim.acc",
        "WBisim.coind_upto",
        "WBisim.paco",
        "WBisim.paco_coind",
        "WBisim.paco_unfold",
        "WBisim.paco_fold",
        "WBisim.paco_mon",
        "WBisim.paco_bot",
        "WBisim.le_paco",
        "WBisim.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("WBisim.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // Park reflexivity on the diagonal candidate: each guard is answered
    // with the SAME successor as witness; the head equations move between
    // `a` and `b` by `Eq.trans`/`Eq.symm` at `St` (no transport needed —
    // `AStep`'s components are first-order equations).
    elab_in(
        &mut env,
        r"theorem wbisim_refl : ∀ u : St, WBisim u u :=
  fun u => WBisim.coind (fun a b => a = b)
    (fun a b h => And.intro
      (fun x s2 hs => Exists.intro s2 (And.intro
        (And.intro (Eq.trans (Eq.symm h) (And.left hs)) (And.right hs)) rfl))
      (fun x t2 ht => Exists.intro t2 (And.intro
        (And.intro (Eq.trans h (And.left ht)) (And.right ht)) rfl)))
    u u rfl",
    )
    .expect("Park coinduction must prove `WBisim u u` through both guarded ∃-conclusions");

    // `.cases`-based refutation that CONSUMES a guard: `loop` can step but
    // `stuck` cannot answer, so the first guarded clause of any
    // `WBisim loop stuck` derivation yields a step out of `stuck` — absurd
    // by computation.
    elab_in(
        &mut env,
        r"theorem wbisim_loop_stuck_false : WBisim St.loop St.stuck → False :=
  fun h => WBisim.cases h False
    (fun g1 g2 => Exists.elim (g1 Act.tau St.loop (And.intro rfl (And.intro rfl rfl)))
      (fun t2 hw => St.noConfusion (And.left (And.left hw))))",
    )
    .expect("`WBisim.cases` must hand the arm applicable guarded clauses");
}

/// GUARDED PREMISES beside the earlier layers: one disjunct carrying a
/// Brick-2 ∃-binder, a plain premise AND a guarded premise — `F_mono` must
/// destructure the disjunct's ∃ layer and map the guarded conjunct inside
/// it (the composite the mutation battery targets).
#[test]
fn test_elab_coinductive_guarded_beside_exists_binder() {
    let mut env = coind_lts_env();
    elab_in(
        &mut env,
        r"coinductive GDiv : St → Prop
| step (q : St) : Step p q → (∀ (r : St), Step q r → GDiv r) → GDiv p",
    )
    .expect("a guarded premise beside an ∃-binder and a plain premise must elaborate");

    // Park: the ∃-witness is `loop`, the guard's conclusion falls back on
    // the candidate. The `Exists.intro` is ascribed to the unfolded ∃-form
    // (the `div_loop` workaround).
    elab_in(
        &mut env,
        r"theorem gdiv_loop : GDiv St.loop :=
  GDiv.coind (fun s => s = St.loop)
    (fun s h => (Exists.intro St.loop (And.intro (And.intro h rfl)
        (fun r hr => And.right hr))
      : ∃ q : St, Step s q ∧ (∀ r : St, Step q r → r = St.loop)))
    St.loop rfl",
    )
    .expect("Park coinduction must prove `GDiv St.loop` through the guarded disjunct");

    // The arm receives witness, plain premise and guarded clause in order.
    elab_in(
        &mut env,
        r"theorem gdiv_stuck_false : GDiv St.stuck → False :=
  fun h => GDiv.cases h False (fun q hs hg => St.noConfusion (And.left hs))",
    )
    .expect("`GDiv.cases` must hand the arm the guarded clause after the plain premise");
}

/// A `mutual` block containing `coinductive` members must refuse LOUDLY.
///
/// MEASURED before the guard (2026-08-26, release binary): the block was
/// silently ACCEPTED and registered NOTHING — `clean check` reported
/// "1 declaration" for a file with a def plus a two-member mutual
/// coinductive, and every downstream use of the vanished predicates failed
/// with an unrelated auto-bound artifact. The classic silently-accepted
/// wrong program. Mutual coinductive predicates are a named future rung of
/// the full-gfp program; until then the block refuses by name, nothing
/// registers, and the codata/codef lanes get the same treatment (their
/// single-decl arms already refuse — a mutual wrapper must not bypass).
#[test]
fn test_mutual_coinductive_refuses_loudly() {
    let mut env = coind_stream_env();
    let err = elab_in(
        &mut env,
        r"mutual
coinductive A : Str → Prop
| step : A s → A s
coinductive B : Str → Prop
| step : B s → B s
end",
    )
    .expect_err("a mutual coinductive block must refuse, never silently vanish");
    let msg = format!("{err:?}");
    assert!(
        msg.contains("mutual") && msg.contains("coinductive"),
        "the refusal must name the construct: {msg}"
    );
    for name in ["A", "B", "A.F", "B.coind"] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "{name} must not be registered by the refused block"
        );
    }
}

/// DECLARATION-PARAMETERS RUNG flagship: a PARAMETRIC relation —
/// `Congr (f : Nat → Nat)` relates conats whose `f`-images agree at every
/// depth. Pre-rung, this exact shape refused through the real check path
/// ("declaration parameters are not supported in v1 — write them as
/// leading indices"; measured 2026-08-26, release binary). Now the row is
/// FIXED through the coinduction under encoding (b) — params are prefix
/// binders on `P` and every companion quantifies over them outermost, the
/// candidate stays `T⃗ → Prop` at fixed `p⃗`, and the recursive
/// substitution happens at `P p⃗` only (see `coinductive_surface_params.rs`
/// for the choice). Pins here: the full family at the fixed row
/// (registered, sorry-free, axiom-free, no `.rec`), GOLDEN kernel types +
/// binder-info spines for the param-threaded companions (the row explicit
/// everywhere, implicit on `.cases` only), a Park proof INSTANTIATING the
/// parameter, the intro at its declared row-first type, and `.cases`
/// consumers at both a generic and a concrete instantiation.
///
/// MUTATION COVERAGE (measured 2026-08-26, both reverted):
/// * param threading dropped from the functor references — `Shape::
///   f_applied` returning `napp(F, [rel])` without the row: all three
///   parameterized accept tests fail inside the CANDIDATE env ("the
///   generated greatest-fixpoint declaration `Congr` failed to
///   elaborate/kernel-check (TypeMismatch …); the declaration is REJECTED
///   rather than partially registered"), every zero-param test stays green
///   — the fail-closed net catches the generator bug before anything
///   registers;
/// * the exactly-the-row validation dropped from `rec_atom` (a premise
///   occurrence allowed to vary the row — the varied argument silently
///   DISCARDED and read as the fixed row): exactly TWO tests fail — the
///   `PVar` battery entry and `decl_param_reject_registers_nothing`, both
///   with "must fail closed with Unsupported, got Ok(Multiple…)". NOTHING
///   kernel-side catches this one (the mutated lowering is well-typed, it
///   just means the wrong thing), so those reject tests are the ONLY net —
///   they are load-bearing, never redundant with the candidate check.
#[test]
fn test_elab_coinductive_decl_param_flagship_congr() {
    use clean_kernel::{BinderInfo, Expr, ExprKind};

    let mut env = coind_conat_env();
    elab_in(
        &mut env,
        r"coinductive Congr (f : Nat → Nat) : CN → CN → Prop
| step : f (a 0) = f (b 0) → Congr f (pred a) (pred b) → Congr f a b",
    )
    .expect("a parameterized coinductive must elaborate (declaration-parameters rung)");

    for name in [
        "Congr",
        "Congr.F",
        "Congr.coind",
        "Congr.F_mono",
        "Congr.unfold",
        "Congr.fold",
        "Congr.step",
        "Congr.cases",
        "Congr.acc",
        "Congr.coind_upto",
        "Congr.paco",
        "Congr.paco_coind",
        "Congr.paco_unfold",
        "Congr.paco_fold",
        "Congr.paco_mon",
        "Congr.paco_bot",
        "Congr.le_paco",
        "Congr.paco_acc",
    ] {
        let n = Name::from_string(name);
        let info = env
            .get_const(&n)
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert!(
            !info.type_.has_sorry(),
            "`{name}` statement must be sorry-free"
        );
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }
    assert!(
        env.get_const(&Name::from_string("Congr.rec")).is_none(),
        "a coinductive predicate must not acquire an induction principle"
    );

    // GOLDEN (parameterized): rendered kernel types + binder-info spines
    // for the row-threading companions — the same pinning mechanism as
    // `test_elab_coinductive_golden_kernel_types`, which stays UNTOUCHED
    // and thereby pins the zero-parameter output byte-stable.
    fn pi_spine(e: &Expr) -> Vec<BinderInfo> {
        let mut out = Vec::new();
        let mut cur = e;
        while let ExprKind::Pi(bd, _, body) = &**cur {
            out.push(bd.info);
            cur = body.as_ref();
        }
        out
    }
    use BinderInfo::{Default as E, Implicit as I};
    // The head probe `x 0` elaborates its literal through `OfNat`; the
    // printer spells that out. One binding keeps the pinned lines readable.
    #[rustfmt::skip]
    let expected: Vec<(&str, String, Vec<BinderInfo>)> = vec![
        ("Congr", "(Nat -> Nat) -> CN -> CN -> Prop".to_string(), vec![E, E, E]),
        ("Congr.F",
         "(Nat -> Nat) -> (CN -> CN -> Prop) -> CN -> CN -> Prop".to_string(),
         vec![E, E, E, E]),
        ("Congr.coind",
         "(f : Nat -> Nat) -> (f1 : CN -> CN -> Prop) \
          -> ((c : CN) -> (c1 : CN) -> f1 c c1 -> Congr.F f f1 c c1) \
          -> ((c : CN) -> (c1 : CN) -> f1 c c1 -> Congr f c c1)".to_string(),
         vec![E, E, E, E, E, E]),
        ("Congr.unfold",
         "(f : Nat -> Nat) -> (c : CN) -> (c1 : CN) -> Congr f c c1 \
          -> Congr.F f (Congr f) c c1".to_string(),
         vec![E, E, E, E]),
        ("Congr.step",
         "(f : Nat -> Nat) -> (c : CN) -> (c1 : CN) \
          -> f (c 0) = f (c1 0) \
          -> Congr f (pred c) (pred c1) -> Congr f c c1".to_string(),
         vec![E, I, I, E, E]),
        ("Congr.cases",
         "(f : Nat -> Nat) -> (c : CN) -> (c1 : CN) -> Congr f c c1 \
          -> ((p : Prop) -> (f (c 0) = f (c1 0) \
          -> Congr f (pred c) (pred c1) -> p) -> p)".to_string(),
         vec![I, I, I, E, E, E]),
    ];
    for (name, want_ty, want_spine) in &expected {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("`{name}` must be registered"));
        assert_eq!(
            info.type_.to_string(),
            *want_ty,
            "`{name}`: the generated statement changed"
        );
        assert_eq!(
            pi_spine(&info.type_),
            *want_spine,
            "`{name}`: the generated binder-info row changed"
        );
    }

    // THE Park run, INSTANTIATING the parameter: reflexivity at every `f`
    // via the diagonal candidate. Genuinely coinductive — the only
    // constructor always recurses, so no finite derivation exists.
    elab_in(
        &mut env,
        r"theorem congr_refl : ∀ f : Nat → Nat, ∀ m : CN, Congr f m m :=
  fun f m => Congr.coind f (fun x y => x = y)
    (fun x y h => And.intro
      (congrArg (fun (q : CN) => f (q 0)) h)
      (congrArg pred h))
    m m rfl",
    )
    .expect("Park coinduction at an instantiated parameter must prove `Congr f m m`");

    // The intro at its declared type: the parameter row leads EXPLICITLY,
    // then the implicit fresh index rows, then the premises.
    elab_in(
        &mut env,
        r"theorem congr_step_use : ∀ f : Nat → Nat, ∀ a b : CN,
    f (a 0) = f (b 0) → Congr f (pred a) (pred b) → Congr f a b :=
  fun f a b h1 h2 => Congr.step f h1 h2",
    )
    .expect("the generated intro must lead with the explicit parameter row");

    // `.cases` at the GENERIC parameter: anti-vacuity head recovery.
    elab_in(
        &mut env,
        r"theorem congr_head : ∀ f : Nat → Nat, ∀ a b : CN,
    Congr f a b → f (a 0) = f (b 0) :=
  fun f a b h => Congr.cases h (f (a 0) = f (b 0)) (fun he hr => he)",
    )
    .expect("`Congr.cases` must hand the arm the premise at the fixed row");

    // `.cases` refutation at a CONCRETE instantiation: under `f := id`,
    // the arm's head equation computes to `1 = 0`.
    elab_in(
        &mut env,
        r"theorem congr_id_one_zero_false : Congr (fun n => n) one zero → False :=
  fun h => Congr.cases h False (fun he hr => Nat.noConfusion he)",
    )
    .expect("`Congr.cases` must refute `Congr id one zero` by head computation");
}

/// DECLARATION-PARAMETERS RUNG: a TWO-parameter fixture pins the row's
/// ORDER end to end — `Agree f g` requires `f`- and `g`-heads to agree
/// along the whole conat, so swapping the row is semantically visible: the
/// diagonal instantiation `Agree f f` proves by Park, the mismatched
/// instantiation refutes through `.cases` by head computation.
#[test]
fn test_elab_coinductive_decl_param_two_params_agree() {
    let mut env = coind_conat_env();
    elab_in(
        &mut env,
        r"coinductive Agree (f : Nat → Nat) (g : Nat → Nat) : CN → Prop
| step : f (m 0) = g (m 0) → Agree f g (pred m) → Agree f g m",
    )
    .expect("a two-parameter coinductive must elaborate with the row in order");

    for name in [
        "Agree",
        "Agree.F",
        "Agree.coind",
        "Agree.F_mono",
        "Agree.unfold",
        "Agree.fold",
        "Agree.step",
        "Agree.cases",
        "Agree.acc",
        "Agree.coind_upto",
        "Agree.paco",
        "Agree.paco_coind",
        "Agree.paco_unfold",
        "Agree.paco_fold",
        "Agree.paco_mon",
        "Agree.paco_bot",
        "Agree.le_paco",
        "Agree.paco_acc",
    ] {
        let n = Name::from_string(name);
        assert!(env.get_const(&n).is_some(), "`{name}` must be registered");
        let deps = env
            .axiom_deps(&n)
            .unwrap_or_else(|| panic!("`{name}` must have an auditable closure"));
        assert!(deps.is_empty(), "`{name}` must be axiom-free, got {deps:?}");
    }

    // Park at the DIAGONAL instantiation `f f`: the candidate is spelled
    // as a reflexive head equation, so no `True` machinery is needed.
    elab_in(
        &mut env,
        r"theorem agree_self : ∀ f : Nat → Nat, ∀ m : CN, Agree f f m :=
  fun f m => Agree.coind f f (fun x => f (x 0) = f (x 0))
    (fun x h => And.intro rfl rfl) m rfl",
    )
    .expect("Park at the diagonal instantiation must prove `Agree f f m`");

    // The MISMATCHED instantiation refutes: the arm's equation computes to
    // `1 = 0`. This is the fixture that keeps a row-order mutation
    // semantically visible (swapped rows would flip which side computes).
    elab_in(
        &mut env,
        r"theorem agree_one_zero_false : Agree (fun n => 1) (fun n => 0) inf → False :=
  fun h => Agree.cases h False (fun he hr => Nat.noConfusion he)",
    )
    .expect("`Agree.cases` must refute the mismatched instantiation");
}

/// DECLARATION-PARAMETERS × GUARDED PREMISES (composition with the
/// "P under ∀/→" rung): the parameter appears in a plain premise AND as
/// the fixed row of a recursive atom UNDER a guard — `F_mono` must map the
/// guarded conjunct at the fixed row inside the param-threaded functor.
#[test]
fn test_elab_coinductive_decl_param_guarded_compose() {
    let mut env = coind_lts_env();
    elab_in(
        &mut env,
        r"coinductive AllPath (t : St) : St → Prop
| step : s = t → (∀ (q : St), Step s q → AllPath t q) → AllPath t s",
    )
    .expect("a parameterized guarded-premise coinductive must elaborate");

    // Park through the guarded functor at a fixed parameter.
    elab_in(
        &mut env,
        r"theorem allpath_loop : AllPath St.loop St.loop :=
  AllPath.coind St.loop (fun s => s = St.loop)
    (fun s h => And.intro h (fun q hq => And.right hq))
    St.loop rfl",
    )
    .expect("Park through the parameterized guarded functor must prove `AllPath loop loop`");

    // `.cases` hands the arm the guarded clause at the FIXED row.
    elab_in(
        &mut env,
        r"theorem allpath_step_out : ∀ t s : St, AllPath t s →
    ∀ q : St, Step s q → AllPath t q :=
  fun t s h => AllPath.cases h (∀ q : St, Step s q → AllPath t q) (fun he hg => hg)",
    )
    .expect("`AllPath.cases` must hand back the guarded clause at the fixed row");
}

/// DECLARATION-PARAMETERS RUNG: a rejected parameterized declaration must
/// leave NOTHING behind — the first constructor is in-envelope, the second
/// varies the parameter row, and the whole family is rolled back.
#[test]
fn test_elab_coinductive_decl_param_reject_registers_nothing() {
    let mut env = coind_stream_env();
    let err = elab_in(
        &mut env,
        r"coinductive PZ (f : Nat → Nat) : Str → Prop
| a : f (shd s) = 0 → PZ f (stl s) → PZ f s
| b : PZ (fun n => n) (stl s) → PZ f s",
    )
    .expect_err("a row-varying later constructor must reject the declaration");
    match err {
        ElabError::Unsupported { feature } => assert!(
            feature.contains("is not the parameter"),
            "the refusal must name the varied row position: {feature}"
        ),
        other => panic!("must fail closed with Unsupported, got {other:?}"),
    }
    for name in [
        "PZ",
        "PZ.F",
        "PZ.coind",
        "PZ.F_mono",
        "PZ.unfold",
        "PZ.fold",
        "PZ.a",
        "PZ.b",
        "PZ.cases",
        "PZ.acc",
        "PZ.coind_upto",
        "PZ.paco",
        "PZ.paco_coind",
        "PZ.paco_unfold",
        "PZ.paco_fold",
        "PZ.paco_mon",
        "PZ.paco_bot",
        "PZ.le_paco",
        "PZ.paco_acc",
    ] {
        assert!(
            env.get_const(&Name::from_string(name)).is_none(),
            "`{name}` must not survive a rejected parameterized coinductive"
        );
    }
}

#[test]
fn interleaved_header_auto_implicits_leave_no_parameter_locals() {
    let env = Environment::with_prelude();
    let mut ctx = ElabCtx::new(&env);
    let before = ctx.locals.len();
    let decl = parse_decl_for_elab(
        "inductive Both (p : α → Prop) (q : β → Prop) : α → β → Prop where | intro {x y} : p x → q y → Both p q x y"
    ).expect("declaration parses");
    ctx.elab_decl(&decl).expect("header elaborates");
    assert_eq!(
        ctx.locals.len(),
        before,
        "explicit parameters must be removed by identity"
    );
    assert_eq!(ctx.auto_implicit_count(), 0);
}
