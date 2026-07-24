// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness + behavior tests for the recursive `BEq` derive (Track L, part 1).
//!
//! These go through the FULL surface pipeline (`elaborate_decl_and_register`),
//! the same one `clean check` uses, then assert:
//!   - the derived `instTyBEq` instance registers and INFER-TYPES against the
//!     genuine mutual recursor `Ty.rec`,
//!   - its `axiom_deps` is EMPTY (no `sorry` / `sorryAx` / trust markers),
//!   - it actually distinguishes genuinely-different values (`==` ⇒ `false`),
//!     proving it is NOT the old always-true `x == x ⇒ true` fallback.

use crate::elaborate_decl_and_register;
use clean_kernel::name::Name;
use clean_kernel::{Environment, TypeChecker};
use clean_parser::parse_decl;

/// Register the recursive `Ty` enum (nested `List Ty` + direct self recursion)
/// with `deriving BEq` and return the environment.
fn ty_env() -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "inductive Ty where \
         | int : Ty \
         | tuple : List Ty -> Ty \
         | vector : Nat -> Ty -> Ty \
         deriving BEq",
    )
    .expect("parse Ty");
    elaborate_decl_and_register(&mut env, &decl).expect("register Ty + derive BEq");
    env
}

#[test]
fn recursive_beq_instance_registers_and_infers() {
    let env = ty_env();
    let inst = Name::from_string("instTyBEq");
    let info = env
        .get_const(&inst)
        .expect("instTyBEq must be registered by the recursive BEq derive");

    // The instance value must INFER-TYPE against the kernel (drives Ty.rec).
    let tc = TypeChecker::new(&env);
    let value = info.value.as_ref().expect("instance has a value");
    let inferred = tc
        .infer_type(value)
        .expect("instTyBEq value must infer-type via the genuine Ty.rec");

    // And the inferred type must be defeq to its declared `BEq Ty` type.
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared BEq Ty type"
    );
}

#[test]
fn recursive_beq_instance_has_no_sorry_axioms() {
    let env = ty_env();
    let inst = Name::from_string("instTyBEq");
    let deps = env
        .axiom_deps(&inst)
        .expect("instTyBEq must be present for axiom_deps");
    assert!(
        deps.is_empty(),
        "recursive BEq instance must have EMPTY axiom_deps (no sorry/trust markers), got {deps:?}"
    );
}

/// Build `(@BEq.beq Ty instTyBEq a b)` and WHNF it; assert it reduces to the
/// expected `Bool` constant. This is the real behavioral gate: the always-true
/// fallback would make every comparison `Bool.true`.
fn beq_reduces_to(env: &Environment, a_src: &str, b_src: &str) -> String {
    use clean_kernel::Expr;
    // Parse the two Ty expressions as defs so they go through elaboration.
    let mut env = env.clone();
    let da = parse_decl(&format!("def __a : Ty := {a_src}")).expect("parse a");
    let db = parse_decl(&format!("def __b : Ty := {b_src}")).expect("parse b");
    elaborate_decl_and_register(&mut env, &da).expect("register a");
    elaborate_decl_and_register(&mut env, &db).expect("register b");

    let beq = Expr::const_(
        Name::from_string("BEq.beq"),
        vec![clean_kernel::Level::zero()],
    );
    let ty = Expr::const_(Name::from_string("Ty"), vec![]);
    let inst = Expr::const_(Name::from_string("instTyBEq"), vec![]);
    let a = Expr::const_(Name::from_string("__a"), vec![]);
    let b = Expr::const_(Name::from_string("__b"), vec![]);
    let app = Expr::app(Expr::app(Expr::app(Expr::app(beq, ty), inst), a), b);
    let tc = TypeChecker::new(&env);
    let whnf = tc.whnf(&app);
    match whnf.kind() {
        clean_kernel::ExprKind::Const(n, _) => n.to_string(),
        other => panic!("expected Bool const after whnf, got {other:?}"),
    }
}

#[test]
fn recursive_beq_distinguishes_direct_self_recursion() {
    let env = ty_env();
    // vector 1 int vs vector 2 int: differ in the Nat scalar field.
    assert_eq!(
        beq_reduces_to(&env, "Ty.vector 1 Ty.int", "Ty.vector 2 Ty.int"),
        "Bool.false",
        "distinct vectors must compare FALSE — not the always-true bug"
    );
    // vector 1 int vs vector 1 (vector 0 int): differ in the recursive Ty field.
    assert_eq!(
        beq_reduces_to(
            &env,
            "Ty.vector 1 Ty.int",
            "Ty.vector 1 (Ty.vector 0 Ty.int)"
        ),
        "Bool.false",
        "vectors with distinct inner Ty subterms must compare FALSE"
    );
    // Equal values compare TRUE.
    assert_eq!(
        beq_reduces_to(&env, "Ty.vector 2 Ty.int", "Ty.vector 2 Ty.int"),
        "Bool.true",
        "equal vectors must compare TRUE"
    );
    // Different constructors compare FALSE.
    assert_eq!(
        beq_reduces_to(&env, "Ty.int", "Ty.vector 0 Ty.int"),
        "Bool.false",
        "distinct constructors must compare FALSE"
    );
}

#[test]
fn recursive_beq_distinguishes_nested_list() {
    let env = ty_env();
    // tuple [int] vs tuple [vector 0 int]: differ in the List element (drives
    // the restored List companion-recursion IH + element BEq).
    assert_eq!(
        beq_reduces_to(
            &env,
            "Ty.tuple (List.cons Ty.int List.nil)",
            "Ty.tuple (List.cons (Ty.vector 0 Ty.int) List.nil)"
        ),
        "Bool.false",
        "tuples with distinct list elements must compare FALSE"
    );
    // Same list ⇒ TRUE.
    assert_eq!(
        beq_reduces_to(
            &env,
            "Ty.tuple (List.cons Ty.int List.nil)",
            "Ty.tuple (List.cons Ty.int List.nil)"
        ),
        "Bool.true",
        "tuples with equal lists must compare TRUE"
    );
    // Different length (cons vs nil) ⇒ FALSE.
    assert_eq!(
        beq_reduces_to(
            &env,
            "Ty.tuple (List.cons Ty.int List.nil)",
            "Ty.tuple List.nil"
        ),
        "Bool.false",
        "tuples with different-length lists must compare FALSE"
    );
}

/// A primary inductive may legitimately live below the `List` namespace.
/// Its constructors are not restored companion rules merely because their
/// printed names begin with `List.`; only exact `List.nil`/`List.cons` belong
/// to the ordinary `List.casesOn` used by the companion minor.
#[test]
fn list_namespace_primary_ctors_are_not_beq_companion_rules() {
    use clean_kernel::{BigNat, Expr, ExprKind, Level, Literal};

    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "namespace List \
         inductive NamespaceTree where \
         | leaf : NamespaceTree \
         | node : Nat -> NamespaceTree -> NamespaceTree \
         | forest : List NamespaceTree -> NamespaceTree \
         deriving BEq \
         end List",
    )
    .expect("parse List.NamespaceTree");
    elaborate_decl_and_register(&mut env, &decl)
        .expect("derive BEq without misclassifying List.NamespaceTree constructors");

    let inst_name = Name::from_string("instList.NamespaceTreeBEq");
    let info = env
        .get_const(&inst_name)
        .expect("namespaced recursive BEq instance must register");
    let value = info.value.as_ref().expect("BEq instance has a value");
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(value)
        .expect("namespaced recursive BEq value must infer-type");
    assert!(tc.is_def_eq(&inferred, &info.type_));
    assert!(
        env.axiom_deps(&inst_name)
            .expect("instance is registered")
            .is_empty(),
        "namespace-collision repair must remain sorry-free"
    );

    let ty = Expr::const_(Name::from_string("List.NamespaceTree"), vec![]);
    let inst = Expr::const_(inst_name, vec![]);
    let leaf = Expr::const_(Name::from_string("List.NamespaceTree.leaf"), vec![]);
    let zero = Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Small(0))));
    let node = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("List.NamespaceTree.node"), vec![]),
            zero,
        ),
        leaf.clone(),
    );
    let beq = Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]);
    let comparison = Expr::app(Expr::app(Expr::app(Expr::app(beq, ty), inst), leaf), node);
    assert!(
        matches!(tc.whnf(&comparison).kind(), ExprKind::Const(name, _) if name == &Name::from_string("Bool.false")),
        "different primary constructors below namespace List must compare false"
    );
}
