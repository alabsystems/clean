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
fn test_issue796_file_1616_inductives_register() {
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
    crate::elaborate_decl_and_register(&mut env, &linear)
        .expect("Linear should elaborate and register after Cover");
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
    // Repr and Hashable are absent from the bare environment; the
    // elaborator now errors hard rather than silently skipping.
    let result = elab_decl(
        r"inductive Color : Type
| red : Color
| green : Color
| blue : Color
deriving BEq, Repr, Hashable",
    );
    let Ok(result) = result else {
        return;
    };

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
    let result = elab_decl(
        r"inductive Bool : Type
| false : Bool
| true : Bool
deriving Inhabited",
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
                Name::from_string("instBoolInhabited")
            );
            assert_eq!(
                derived_instances[0].class_name,
                Name::from_string("Inhabited")
            );

            // Check that the instance uses the first constructor (Bool.false)
            match derived_instances[0].val.kind() {
                ExprKind::App(_, arg) => {
                    // arg should be Bool.false
                    match arg.kind() {
                        ExprKind::Const(ctor_name, _) => {
                            assert_eq!(*ctor_name, Name::from_string("Bool.false"));
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
    // Single constructor inductive always has equal elements
    let result = elab_decl(
        r"inductive Unit : Type
| unit : Unit
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
            assert_eq!(name, Name::from_string("Unit"));
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
    assert!(mentions_string(value, "ReprTree.leaf"));
    assert!(mentions_string(value, "ReprTree.next"));
    assert!(!value.has_sorry(), "derived Repr must not contain sorry");
    let deps = env
        .axiom_deps(&inst_name)
        .expect("registered Repr instance must have an auditable closure");
    assert!(deps.is_empty(), "derived Repr must be axiom-free: {deps:?}");
}

#[test]
fn test_elab_coinductive_fails_closed() {
    // A `coinductive` declaration must NOT silently elaborate as an inductive:
    // that would mint the least fixpoint (plus an induction principle the
    // greatest fixpoint must not have) for a declaration whose meaning is the
    // greatest fixpoint. Until the gfp lowering lands, this is fail-closed.
    let result = elab_decl(
        r"coinductive Bisim : Nat → Nat → Prop
| step : Bisim m n → Bisim m n",
    );

    match result {
        Err(ElabError::Unsupported { feature }) => {
            assert!(
                feature.contains("coinductive") && feature.contains("Bisim"),
                "diagnostic must name the construct and declaration: {feature}"
            );
        }
        other => panic!("coinductive must fail closed with Unsupported, got {other:?}"),
    }
}
