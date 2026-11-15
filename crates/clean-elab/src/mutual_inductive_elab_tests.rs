// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests for `mutual … end` blocks of *inductive* declarations
//! (bug #31: such blocks silently registered 0 declarations).
//!
//! These go through the FULL surface pipeline (`elaborate_decl_and_register`),
//! the same one `clean check` uses, and assert:
//!   - both cross-referencing inductive TYPES and their CONSTRUCTORS register,
//!   - the registered types are usable in `def`s (values kernel-infer),
//!   - a genuinely-broken family (constructor referencing an undefined type) is
//!     REJECTED loudly rather than silently dropped,
//!   - a plain single `inductive` is unaffected.

use crate::elaborate_decl_and_register;
use clean_kernel::{BigNat, Environment, Expr, ExprKind, Name, TypeChecker};
use clean_parser::parse_file;

/// Elaborate + register every decl in `code`, panicking on the first failure.
fn elab_all(code: &str) -> Environment {
    let mut env = Environment::with_prelude();
    let decls = parse_file(code).expect("should parse");
    for (i, decl) in decls.iter().enumerate() {
        elaborate_decl_and_register(&mut env, decl)
            .unwrap_or_else(|e| panic!("decl {i} failed to elaborate: {e:?}"));
    }
    env
}

const EVEN_ODD_SRC: &str = r#"
mutual
inductive Even where
  | zero
  | succ : Odd -> Even
inductive Odd where
  | succ : Even -> Odd
end
"#;

#[test]
fn test_mutual_inductive_registers_both_types() {
    let env = elab_all(EVEN_ODD_SRC);
    assert!(
        env.get_inductive(&Name::from_string("Even")).is_some(),
        "Even inductive must register"
    );
    assert!(
        env.get_inductive(&Name::from_string("Odd")).is_some(),
        "Odd inductive must register"
    );
    // The mutual family must be linked: each type sees the other in all_names.
    let even = env
        .get_inductive(&Name::from_string("Even"))
        .expect("Even present");
    assert_eq!(even.all_names.len(), 2, "Even belongs to a 2-type family");
}

#[test]
fn test_mutual_inductive_registers_constructors() {
    let env = elab_all(EVEN_ODD_SRC);
    for ctor in ["Even.zero", "Even.succ", "Odd.succ"] {
        assert!(
            env.get_constructor(&Name::from_string(ctor)).is_some(),
            "constructor {ctor} must register"
        );
    }
}

#[test]
fn test_mutual_inductive_constructors_usable_in_defs() {
    // The whole followup file from bug #31: the constructors must be usable to
    // build cross-referencing values that kernel-infer against their types.
    let src = format!(
        "{EVEN_ODD_SRC}\n\
         def e0 : Even := Even.zero\n\
         def o1 : Odd := Odd.succ Even.zero\n\
         def e2 : Even := Even.succ (Odd.succ Even.zero)\n"
    );
    let env = elab_all(&src);
    let tc = TypeChecker::new(&env);
    for name in ["e0", "o1", "e2"] {
        let info = env
            .get_const(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must register"));
        let value = info
            .value
            .as_ref()
            .unwrap_or_else(|| panic!("{name} must have a value"));
        let inferred = tc
            .infer_type(value)
            .unwrap_or_else(|e| panic!("infer_type({name}) failed: {e:?}"));
        assert!(
            tc.is_def_eq(&inferred, &info.type_),
            "{name}: inferred value type not def-eq to declared type"
        );
    }
}

const NESTED_RECURSIVE_UNIVERSE_SRC: &str = r#"
mutual
inductive NestedExpr where
  | leaf
  | many : List NestedExpr -> NestedExpr
  | pair : List (NestedExpr × NestedAct) -> NestedExpr
  | enabled : NestedAct -> NestedExpr
inductive NestedAct where
  | done
  | expr : NestedExpr -> NestedAct
  | many : List NestedAct -> NestedAct
end
"#;

#[test]
fn test_nested_recursive_fields_do_not_generalize_the_family_universe() {
    let env = elab_all(NESTED_RECURSIVE_UNIVERSE_SRC);
    for name in ["NestedExpr", "NestedAct"] {
        let ind = env
            .get_inductive(&Name::from_string(name))
            .unwrap_or_else(|| panic!("{name} must register"));
        assert!(
            ind.level_params.is_empty(),
            "a family containing only concrete and recursive fields stays monomorphic: {:?}",
            ind.level_params
        );
        let mut result = &ind.type_;
        while let ExprKind::Pi(_, _, body) = result.kind() {
            result = body;
        }
        assert!(
            matches!(result.kind(), ExprKind::Sort(level) if level == &clean_kernel::Level::succ(clean_kernel::Level::zero())),
            "{name} must infer `Type`, got {:?}",
            ind.type_
        );
    }
}

const MUTUAL_CTOR_UNIVERSE_SRC: &str = r#"
mutual
inductive UniverseExpr where
  | nil
  | node : Type u -> UniverseAct -> UniverseExpr
inductive UniverseAct where
  | nil
  | expr : UniverseExpr -> UniverseAct
end
def universeNat : UniverseExpr := UniverseExpr.node Nat UniverseAct.nil
"#;

#[test]
fn test_constructor_universe_is_declared_and_recursive_constants_receive_it() {
    let env = elab_all(MUTUAL_CTOR_UNIVERSE_SRC);
    let expr = env
        .get_inductive(&Name::from_string("UniverseExpr"))
        .expect("UniverseExpr must register");
    let act = env
        .get_inductive(&Name::from_string("UniverseAct"))
        .expect("UniverseAct must register");
    assert_eq!(
        expr.level_params.len(),
        1,
        "the constructor's auto-bound named universe is part of the shared family interface"
    );
    assert_eq!(
        act.level_params, expr.level_params,
        "every member of a mutual family has the same universe interface"
    );
    assert!(
        expr.level_params
            .iter()
            .all(|name| !name.to_string().starts_with('?')),
        "metavariable spellings must never be registered: {:?}",
        expr.level_params
    );

    let info = env
        .get_const(&Name::from_string("universeNat"))
        .expect("the generalized constructors must be usable");
    let value = info.value.as_ref().expect("universeNat must have a value");
    let inferred = TypeChecker::new(&env)
        .infer_type(value)
        .expect("the constructor application must kernel-infer");
    assert!(
        TypeChecker::new(&env).is_def_eq(&inferred, &info.type_),
        "the constructor application must inhabit its registered type"
    );
}

/// Ordinary mutual recursors expose the complete minor telescope on every
/// member, but each `RecursorVal.rules` stores only that member's constructor
/// slice. Match lowering must concatenate those slices in `all_names` order;
/// it must not mistake ordinary sibling rules for restored nested companions.
#[test]
fn test_ordinary_mutual_matches_aggregate_member_rule_slices() {
    let src = format!(
        "{EVEN_ODD_SRC}\n\
         def evenTag : Even -> Nat\n\
           | Even.zero => 0\n\
           | Even.succ _ => 1\n\
         def oddTag : Odd -> Nat\n\
           | Odd.succ _ => 2\n\
         def oddTagDo : Odd -> Id Nat := fun x => do\n\
           match x with\n\
           | Odd.succ _ => return 3\n"
    );
    let env = elab_all(&src);
    let tc = TypeChecker::new(&env);

    let even_zero = Expr::const_(Name::from_string("Even.zero"), vec![]);
    let odd_succ_zero = Expr::app(
        Expr::const_(Name::from_string("Odd.succ"), vec![]),
        even_zero.clone(),
    );
    let even_succ = Expr::app(
        Expr::const_(Name::from_string("Even.succ"), vec![]),
        odd_succ_zero.clone(),
    );
    let cases = [
        ("evenTag", even_zero, 0),
        ("evenTag", even_succ, 1),
        ("oddTag", odd_succ_zero.clone(), 2),
        ("oddTagDo", odd_succ_zero, 3),
    ];
    for (function, arg, expected) in cases {
        let value = Expr::app(Expr::const_(Name::from_string(function), vec![]), arg);
        assert!(
            matches!(tc.whnf(&value).kind(), ExprKind::Lit(clean_kernel::Literal::Nat(BigNat::Small(n))) if *n == expected),
            "{function} must reduce through the ordinary mutual minor ordering"
        );
    }
}

#[test]
fn test_mutual_inductive_broken_member_is_rejected() {
    // `Baz` is undefined: the family is ill-formed and MUST be rejected — not
    // silently dropped (the soundness-adjacent silent-accept bug).
    let src = r#"
mutual
inductive Foo where
  | mk : Baz -> Foo
inductive Bar where
  | mk : Foo -> Bar
end
"#;
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).expect("should parse");
    let result = decls
        .iter()
        .try_for_each(|decl| elaborate_decl_and_register(&mut env, decl).map(|_| ()));
    assert!(
        result.is_err(),
        "a mutual block with an undefined type reference must be REJECTED, not silently accepted"
    );
    // And nothing from the rejected family may leak into the environment.
    assert!(
        env.get_inductive(&Name::from_string("Foo")).is_none(),
        "rejected Foo must not be registered"
    );
    assert!(
        env.get_inductive(&Name::from_string("Bar")).is_none(),
        "rejected Bar must not be registered"
    );
}

#[test]
fn test_single_inductive_still_registers() {
    let env = elab_all("inductive Wrap where\n  | mk : Nat -> Wrap\n");
    assert!(
        env.get_inductive(&Name::from_string("Wrap")).is_some(),
        "single inductive must still register"
    );
    assert!(
        env.get_constructor(&Name::from_string("Wrap.mk")).is_some(),
        "single inductive constructor must still register"
    );
}

// ── auto-bound implicits inside a `mutual` block ─────────────────────────────
//
// Lean auto-binds a constructor's unknown identifiers as IMPLICIT constructor
// arguments. Measured against Lean v4.30.0-rc2 on the reproducer below:
//
//   Env.cons : {t : Bool} → {y : Type} → Lift t y → Env [t]
//
// The single-`inductive` path did this; the `mutual` path did not, so the
// auto-bound fvars survived into the registered constructor and the kernel
// refused the family with "Env.cons contains free variables (fvar ids [2, 3])".

/// tests/lean4_compat/lean4_tests/1112.lean, verbatim.
const AUTO_IMPLICIT_SRC: &str = r#"
mutual
    inductive Lift : Bool -> Type -> Type 2

    inductive Env : List Bool -> Type 2
    | cons : Lift t y -> Env [t]
end
"#;

/// Peel `n` leading `Pi` binders, returning each binder's `(BinderInfo, domain)`.
fn leading_binders(mut ty: &Expr, n: usize) -> Vec<(clean_kernel::BinderInfo, Expr)> {
    let mut out = Vec::new();
    for _ in 0..n {
        let ExprKind::Pi(info, domain, body) = ty.kind() else {
            break;
        };
        out.push((info.info, domain.as_ref().clone()));
        ty = body;
    }
    out
}

#[test]
fn test_mutual_inductive_captures_constructor_auto_implicits() {
    let env = elab_all(AUTO_IMPLICIT_SRC);
    let cons = env
        .get_constructor(&Name::from_string("Env.cons"))
        .expect("Env.cons must register");

    // Lean: `{t : Bool} → {y : Type} → …`. Both binders IMPLICIT, in that order.
    let binders = leading_binders(&cons.type_, 2);
    assert_eq!(
        binders.len(),
        2,
        "Env.cons must open with the two auto-bound implicits, got {:?}",
        cons.type_
    );
    for (i, (info, _)) in binders.iter().enumerate() {
        assert_eq!(
            *info,
            clean_kernel::BinderInfo::Implicit,
            "auto-bound binder {i} must be implicit, not {info:?}"
        );
    }
    assert!(
        matches!(binders[0].1.kind(), ExprKind::Const(n, _) if n.to_string() == "Bool"),
        "first auto-implicit is `t : Bool`, got {:?}",
        binders[0].1
    );
    assert!(
        matches!(binders[1].1.kind(), ExprKind::Sort(l) if !l.is_zero()),
        "second auto-implicit is `y : Type`, got {:?}",
        binders[1].1
    );
    // Constructor-level auto-implicits are FIELDS, never parameters (Lean prints
    // `number of parameters: 0` for both members of this family).
    assert_eq!(cons.num_params, 0, "the family has no parameters");
}

#[test]
fn test_mutual_inductive_auto_implicit_constructor_is_usable() {
    // Lean ACCEPTS this application (`t`/`y` inferred from `l`).
    let src =
        format!("{AUTO_IMPLICIT_SRC}\ndef usePos (l : Lift true Nat) : Env [true] := Env.cons l\n");
    let env = elab_all(&src);
    let tc = TypeChecker::new(&env);
    let info = env
        .get_const(&Name::from_string("usePos"))
        .expect("usePos must register");
    let value = info.value.as_ref().expect("usePos must have a value");
    let inferred = tc
        .infer_type(value)
        .expect("usePos value must kernel-infer");
    assert!(
        tc.is_def_eq(&inferred, &info.type_),
        "usePos: inferred value type not def-eq to declared type"
    );
}

#[test]
fn test_mutual_inductive_auto_implicit_wrong_index_is_rejected() {
    // Lean REJECTS: `Env.cons l` with `l : Lift true Nat` has index `[true]`.
    // A constructor that captured NO implicits, or captured them wrongly, would
    // let this through — so this is the direction that matters.
    let src = format!(
        "{AUTO_IMPLICIT_SRC}\ndef useNeg (l : Lift true Nat) : Env [false] := Env.cons l\n"
    );
    let mut env = Environment::with_prelude();
    let decls = parse_file(&src).expect("should parse");
    let result = decls
        .iter()
        .try_for_each(|decl| elaborate_decl_and_register(&mut env, decl).map(|_| ()));
    assert!(
        result.is_err(),
        "`Env.cons l : Env [false]` is ill-typed and must be REJECTED"
    );
}

#[test]
fn test_mutual_inductive_auto_implicits_do_not_leak_across_siblings() {
    // Lean: `L1.one : {t : Bool} → L1 t` and `L2.two : {s : Bool} → L2 s` —
    // ONE implicit each. A block-scoped (rather than constructor-scoped) capture
    // would give the later constructor both.
    let env = elab_all(
        "mutual\n\
         inductive L1 : Bool -> Type 1\n\
         | one : L1 t\n\
         inductive L2 : Bool -> Type 1\n\
         | two : L2 s\n\
         end\n",
    );
    for ctor in ["L1.one", "L2.two"] {
        let val = env
            .get_constructor(&Name::from_string(ctor))
            .unwrap_or_else(|| panic!("{ctor} must register"));
        // Counted as `num_params + num_fields` rather than `num_fields` alone:
        // Clean's kernel promotes a FIXED index to a parameter inside
        // `add_inductive` (`fixed_indices_to_params`), so `L1.one`'s single
        // binder lands in `num_params`, not `num_fields`. Lean prints
        // `number of parameters: 0` for the same family — a convention
        // difference in the split, not in the constructor's type. The sum is
        // what a cross-sibling leak would move (it would read 2).
        assert_eq!(
            val.num_params + val.num_fields,
            1,
            "{ctor} owns exactly one auto-bound implicit, got type {:?}",
            val.type_
        );
        let binders = leading_binders(&val.type_, 2);
        assert_eq!(
            binders.len(),
            1,
            "{ctor} must have exactly ONE leading binder, got {:?}",
            val.type_
        );
    }
}

#[test]
fn test_mutual_inductive_auto_implicit_does_not_escape_the_block() {
    // An auto-implicit left in `self.locals` would silently resolve a bare `t`
    // in the NEXT declaration. Lean: `Unknown identifier `t``.
    let src = "mutual\n\
               inductive L1 : Bool -> Type 1\n\
               | one : L1 t\n\
               inductive L2 : Bool -> Type 1\n\
               | two : L2 s\n\
               end\n\
               def afterBlock : Bool := t\n";
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).expect("should parse");
    let result = decls
        .iter()
        .try_for_each(|decl| elaborate_decl_and_register(&mut env, decl).map(|_| ()));
    assert!(
        result.is_err(),
        "`t` must not survive the mutual block into a later value position"
    );
}

#[test]
fn test_mutual_inductive_header_auto_implicit_is_refused_in_the_open() {
    // Lean ACCEPTS this (`HA : {α : Type} → α → Type 1`, 0 parameters) by
    // binding the head auto-implicit as an implicit INDEX. That threading is not
    // ported, so this is a known over-refusal — but it must be a NAMED refusal,
    // not a kernel free-variable report, and nothing may register.
    let src = "mutual\n\
               inductive HA : a -> Type 1\n\
               | mk : HA x\n\
               inductive HB : Type 1\n\
               | mk : HB\n\
               end\n";
    let mut env = Environment::with_prelude();
    let decls = parse_file(src).expect("should parse");
    let result = decls
        .iter()
        .try_for_each(|decl| elaborate_decl_and_register(&mut env, decl).map(|_| ()));
    let err = result.expect_err("head auto-implicits are not supported on the mutual path");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("TYPE HEAD"),
        "the refusal must name the unsupported feature, got {rendered}"
    );
    assert!(
        env.get_inductive(&Name::from_string("HA")).is_none(),
        "nothing from a refused family may register"
    );
}
