// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Soundness + behavior tests for Track P:
//!   - PURE DIRECT self-recursion (`num_motives = 1`) `BEq` — the case Wave-3's
//!     nested-`List` builder did not cover, where the old code fell back to the
//!     always-true `λ _ _ => Bool.true` bug.
//!   - MULTI-FIELD non-recursive `DecidableEq` (chained `congrArg`/`Eq.trans`).
//!   - DIRECT self-recursive `DecidableEq` driven by the type's own recursor.
//!
//! All tests go through the FULL surface pipeline (`elaborate_decl_and_register`,
//! the same one `clean check` uses), then assert the derived instance INFER-TYPES
//! against the genuine kernel recursor, has EMPTY `axiom_deps` (no `sorry` /
//! trust markers), and actually distinguishes / decides values.

use crate::elaborate_decl_and_register;
use clean_kernel::name::Name;
use clean_kernel::{Environment, Expr, ExprKind, Level, TypeChecker};
use clean_parser::parse_decl;

/// Whether `e` references a `sorry`/`sorryAx` constant anywhere.
fn mentions_sorry(e: &Expr) -> bool {
    fn name_is_sorry(n: &Name) -> bool {
        let s = n.to_string();
        s == "sorry" || s == "sorryAx" || s.ends_with(".sorry") || s.ends_with(".sorryAx")
    }
    match e.kind() {
        ExprKind::Const(n, _) => name_is_sorry(n),
        ExprKind::App(f, a) => mentions_sorry(f) || mentions_sorry(a),
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => mentions_sorry(t) || mentions_sorry(b),
        _ => false,
    }
}

/// Register a PURE direct self-recursive enum (NO `List Self`, so `num_motives=1`)
/// with `deriving BEq`.
fn direct_beq_env() -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "inductive Ty where \
         | int : Ty \
         | vector : Nat -> Ty -> Ty \
         deriving BEq",
    )
    .expect("parse Ty");
    elaborate_decl_and_register(&mut env, &decl).expect("register Ty + derive BEq");
    env
}

#[test]
fn direct_recursive_beq_registers_and_infers_no_sorry() {
    let env = direct_beq_env();
    let inst = Name::from_string("instTyBEq");
    let info = env
        .get_const(&inst)
        .expect("instTyBEq must be registered by the direct-recursive BEq derive");
    let value = info.value.as_ref().expect("instance has a value");

    assert!(
        !mentions_sorry(value),
        "direct-recursive BEq derive must NOT emit sorry/sorryAx"
    );

    // Must INFER-TYPE against the genuine single-motive Ty.rec.
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(value)
        .expect("instTyBEq value must infer-type via the genuine Ty.rec (num_motives=1)");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared BEq Ty type"
    );

    // Empty axiom_deps: no sorry, no trust markers.
    let deps = env
        .axiom_deps(&inst)
        .expect("instTyBEq present for axiom_deps");
    assert!(
        deps.is_empty(),
        "direct-recursive BEq instance must have EMPTY axiom_deps, got {deps:?}"
    );
}

/// WHNF `@BEq.beq Ty instTyBEq a b` to a Bool const.
fn beq_reduces_to(env: &Environment, a_src: &str, b_src: &str) -> String {
    let mut env = env.clone();
    let da = parse_decl(&format!("def __a : Ty := {a_src}")).expect("parse a");
    let db = parse_decl(&format!("def __b : Ty := {b_src}")).expect("parse b");
    elaborate_decl_and_register(&mut env, &da).expect("register a");
    elaborate_decl_and_register(&mut env, &db).expect("register b");

    let beq = Expr::const_(Name::from_string("BEq.beq"), vec![Level::zero()]);
    let ty = Expr::const_(Name::from_string("Ty"), vec![]);
    let inst = Expr::const_(Name::from_string("instTyBEq"), vec![]);
    let a = Expr::const_(Name::from_string("__a"), vec![]);
    let b = Expr::const_(Name::from_string("__b"), vec![]);
    let app = Expr::app(Expr::app(Expr::app(Expr::app(beq, ty), inst), a), b);
    let tc = TypeChecker::new(&env);
    match tc.whnf(&app).kind() {
        ExprKind::Const(n, _) => n.to_string(),
        other => panic!("expected Bool const after whnf, got {other:?}"),
    }
}

#[test]
fn direct_recursive_beq_distinguishes() {
    let env = direct_beq_env();
    // Differ in the Nat scalar field of `vector`.
    assert_eq!(
        beq_reduces_to(&env, "Ty.vector 1 Ty.int", "Ty.vector 2 Ty.int"),
        "Bool.false",
        "distinct vectors must compare FALSE — not the always-true fallback bug"
    );
    // Differ in the recursive Ty sub-field.
    assert_eq!(
        beq_reduces_to(
            &env,
            "Ty.vector 1 Ty.int",
            "Ty.vector 1 (Ty.vector 0 Ty.int)"
        ),
        "Bool.false",
        "distinct inner Ty sub-terms must compare FALSE (IH drives recursion)"
    );
    // Equal ⇒ TRUE.
    assert_eq!(
        beq_reduces_to(&env, "Ty.vector 2 Ty.int", "Ty.vector 2 Ty.int"),
        "Bool.true",
        "equal vectors must compare TRUE"
    );
    // Different constructor ⇒ FALSE.
    assert_eq!(
        beq_reduces_to(&env, "Ty.int", "Ty.vector 0 Ty.int"),
        "Bool.false",
        "distinct constructors must compare FALSE"
    );
}

// ---------------------------------------------------------------------------
// Multi-field non-recursive DecidableEq
// ---------------------------------------------------------------------------

fn pair_deceq_env() -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "inductive Pair where \
         | mk : Nat -> Nat -> Pair \
         | solo : Nat -> Pair \
         deriving DecidableEq",
    )
    .expect("parse Pair");
    elaborate_decl_and_register(&mut env, &decl).expect("register Pair + derive DecidableEq");
    env
}

/// `if (a = b) then (1:Nat) else 0` reduced to a Nat literal debug string.
fn pick_reduces(env: &Environment, ty: &str, a_src: &str, b_src: &str) -> String {
    let _ = ty;
    let mut env = env.clone();
    let d = parse_decl(&format!(
        "def __pick : Nat := if ({a_src} = {b_src}) then 1 else 0"
    ))
    .expect("parse pick");
    elaborate_decl_and_register(&mut env, &d).expect("register pick");
    let pick = Expr::const_(Name::from_string("__pick"), vec![]);
    let tc = TypeChecker::new(&env);
    format!("{:?}", tc.whnf(&pick).kind())
}

#[test]
fn multifield_decidable_eq_no_sorry_and_decides() {
    let env = pair_deceq_env();
    let inst = Name::from_string("instPairDecidableEq");
    let info = env
        .get_const(&inst)
        .expect("instPairDecidableEq must be registered");
    let value = info.value.as_ref().expect("instance value");
    assert!(
        !mentions_sorry(value),
        "multi-field DecidableEq must NOT emit sorry"
    );
    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(value)
        .expect("instPairDecidableEq must infer-type via casesOn/noConfusion");
    assert!(tc.is_def_eq(&inferred, &info.type_));
    let deps = env
        .axiom_deps(&inst)
        .expect("instPairDecidableEq present for axiom_deps");
    assert!(
        deps.is_empty(),
        "multi-field DecidableEq must have EMPTY axiom_deps, got {deps:?}"
    );

    // Behavior: both fields must matter.
    assert!(pick_reduces(&env, "Pair", "Pair.mk 1 2", "Pair.mk 1 2").contains("Small(1)"));
    // second field differs ⇒ 0 (would be a bug if only the first field were checked).
    assert!(pick_reduces(&env, "Pair", "Pair.mk 1 2", "Pair.mk 1 3").contains("Small(0)"));
    // first field differs ⇒ 0.
    assert!(pick_reduces(&env, "Pair", "Pair.mk 1 2", "Pair.mk 9 2").contains("Small(0)"));
    // different ctor ⇒ 0.
    assert!(pick_reduces(&env, "Pair", "Pair.mk 1 2", "Pair.solo 1").contains("Small(0)"));
    // single-field ctor equal ⇒ 1.
    assert!(pick_reduces(&env, "Pair", "Pair.solo 5", "Pair.solo 5").contains("Small(1)"));
}

// ---------------------------------------------------------------------------
// Direct self-recursive DecidableEq
// ---------------------------------------------------------------------------

fn ty_deceq_env() -> Environment {
    let mut env = Environment::with_prelude();
    let decl = parse_decl(
        "inductive Ty where \
         | int : Ty \
         | vector : Nat -> Ty -> Ty \
         deriving DecidableEq",
    )
    .expect("parse Ty");
    elaborate_decl_and_register(&mut env, &decl).expect("register Ty + derive DecidableEq");
    env
}

#[test]
fn recursive_decidable_eq_no_sorry_infers_and_decides() {
    let env = ty_deceq_env();
    let inst = Name::from_string("instTyDecidableEq");
    let info = env
        .get_const(&inst)
        .expect("instTyDecidableEq must be registered by the recursive DecidableEq derive");
    let value = info.value.as_ref().expect("instance value");
    assert!(
        !mentions_sorry(value),
        "recursive DecidableEq must NOT emit sorry — this is the Track P obligation"
    );

    let tc = TypeChecker::new(&env);
    let inferred = tc
        .infer_type(value)
        .expect("instTyDecidableEq must infer-type via the genuine Ty.rec");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "inferred type must match declared DecidableEq Ty type"
    );
    let deps = env
        .axiom_deps(&inst)
        .expect("instTyDecidableEq present for axiom_deps");
    assert!(
        deps.is_empty(),
        "recursive DecidableEq must have EMPTY axiom_deps, got {deps:?}"
    );

    // Behavior: structural recursion decides nested terms.
    assert!(
        pick_reduces(&env, "Ty", "Ty.vector 1 Ty.int", "Ty.vector 1 Ty.int").contains("Small(1)")
    );
    assert!(
        pick_reduces(&env, "Ty", "Ty.vector 1 Ty.int", "Ty.vector 2 Ty.int").contains("Small(0)")
    );
    assert!(pick_reduces(&env, "Ty", "Ty.int", "Ty.vector 1 Ty.int").contains("Small(0)"));
    // deep recursion: inner Nat differs.
    assert!(pick_reduces(
        &env,
        "Ty",
        "Ty.vector 1 (Ty.vector 2 Ty.int)",
        "Ty.vector 1 (Ty.vector 9 Ty.int)"
    )
    .contains("Small(0)"));
    // deep recursion: equal ⇒ 1.
    assert!(pick_reduces(
        &env,
        "Ty",
        "Ty.vector 1 (Ty.vector 2 Ty.int)",
        "Ty.vector 1 (Ty.vector 2 Ty.int)"
    )
    .contains("Small(1)"));
}
