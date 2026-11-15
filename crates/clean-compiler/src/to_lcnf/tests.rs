// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for kernel Expr to L5CNF conversion.

use super::lower::{
    classify_expr_arg, collect_app_args, expr_to_arg, expr_to_let_value, is_singleton_type,
    ExprArgClass,
};
use super::mentions::code_mentions_name;
use super::*;
use crate::error::CompilerError;
use crate::lcnf::{Alt, Arg, Param};
use clean_kernel::env::TrustedEnvExt;
use clean_kernel::inductive::mentions_name;
use clean_kernel::{BinderInfo, Declaration, ExprKind, Level};

pub(super) fn make_env() -> Environment {
    Environment::default()
}

pub(super) fn add_axiom(env: &mut Environment, name: &str, ty: Expr) -> Name {
    let name = Name::from_string(name);
    let decl = Declaration::Axiom {
        name: name.clone(),
        level_params: vec![],
        type_: ty,
    };
    env.add_decl(decl).unwrap();
    name
}

#[test]
fn test_fvar_gen() {
    let mut id_gen = FVarIdGen::new();
    assert_eq!(id_gen.fresh(), FVarId::new(0));
    assert_eq!(id_gen.fresh(), FVarId::new(1));
    assert_eq!(id_gen.fresh(), FVarId::new(2));
}

#[test]
fn test_bvar_lookup() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    // Push some binders
    let fv0 = ctx.push_binder();
    let fv1 = ctx.push_binder();
    let fv2 = ctx.push_binder();

    // BVar(0) is innermost (fv2)
    assert_eq!(ctx.lookup_bvar(0), Some(fv2));
    // BVar(1) is next (fv1)
    assert_eq!(ctx.lookup_bvar(1), Some(fv1));
    // BVar(2) is outermost (fv0)
    assert_eq!(ctx.lookup_bvar(2), Some(fv0));
    // BVar(3) is out of scope
    assert_eq!(ctx.lookup_bvar(3), None);
}

#[test]
fn test_collect_app_args() {
    // f a b c
    let f = Expr::const_str("f");
    let a = Expr::const_str("a");
    let b = Expr::const_str("b");
    let c = Expr::const_str("c");

    let app1 = Expr::app(f.clone(), a.clone());
    let app2 = Expr::app(app1, b.clone());
    let app3 = Expr::app(app2, c.clone());

    let (head, args) = collect_app_args(&app3);
    assert!(matches!(head.kind(), ExprKind::Const(_, _)));
    assert_eq!(args.len(), 3);
}

#[test]
fn test_literal_conversion() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    let lit_expr = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
        clean_kernel::BigNat::Small(42),
    )));
    let (value, _ty) = expr_to_let_value(&mut ctx, &lit_expr).unwrap();

    assert!(matches!(
        value,
        LetValue::Lit(clean_kernel::Literal::Nat(n)) if n.to_u64() == Some(42)
    ));
}

#[test]
fn test_const_conversion() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    let const_expr = Expr::const_str("Nat.zero");
    let (value, _ty) = expr_to_let_value(&mut ctx, &const_expr).unwrap();

    assert!(matches!(value, LetValue::Const { .. }));
}

#[test]
fn test_is_erasable_sorts() {
    let env = make_env();

    // Sort expressions are always erasable
    assert!(is_erasable(&env, &Expr::sort(Level::zero())));
    assert!(is_erasable(&env, &Expr::sort(Level::succ(Level::zero()))));

    // SProp is always erasable
    assert!(is_erasable(&env, &Expr::from_kind(ExprKind::SProp)));

    // Non-type expressions are not erasable by default
    let nat_lit = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
        clean_kernel::BigNat::Small(42),
    )));
    assert!(!is_erasable(&env, &nat_lit));
}

#[test]
fn test_classify_expr_arg_prop_const() {
    let mut env = make_env();
    let prop_name = add_axiom(&mut env, "MyProp", Expr::prop());
    let prop_const = Expr::const_(prop_name, Vec::<Level>::new());

    assert_eq!(classify_expr_arg(&env, &prop_const), ExprArgClass::Erased);
    assert!(is_erasable(&env, &prop_const));
    assert!(matches!(
        expr_to_arg(&mut LcnfContext::new(&env), &prop_const).unwrap(),
        Arg::Erased
    ));
}

#[test]
fn test_classify_expr_arg_type_const() {
    let mut env = make_env();
    let ty_name = add_axiom(&mut env, "MyType", Expr::type_());
    let ty_const = Expr::const_(ty_name.clone(), Vec::<Level>::new());

    assert_eq!(classify_expr_arg(&env, &ty_const), ExprArgClass::Type);
    assert!(is_erasable(&env, &ty_const));
    assert!(matches!(
        expr_to_arg(&mut LcnfContext::new(&env), &ty_const).unwrap(),
        Arg::Type(expr) if matches!(expr.kind(), ExprKind::Const(name, _) if *name == ty_name)
    ));
}

#[test]
fn test_classify_expr_arg_normal_const() {
    let mut env = make_env();
    let ty_name = add_axiom(&mut env, "MyType", Expr::type_());
    let val_name = add_axiom(
        &mut env,
        "myVal",
        Expr::const_(ty_name, Vec::<Level>::new()),
    );
    let val_const = Expr::const_(val_name, Vec::<Level>::new());

    assert_eq!(classify_expr_arg(&env, &val_const), ExprArgClass::Normal);
    assert!(!is_erasable(&env, &val_const));
}

#[test]
fn test_recursion_detection() {
    // Test that mentions_name correctly detects recursion
    let name = Name::from_string("Nat.succ");

    // Non-recursive: body doesn't mention the name
    let non_recursive_body = Expr::const_str("Nat.zero");
    assert!(!mentions_name(&non_recursive_body, &name));

    // Recursive: body mentions its own name (simulating succ n = succ (pred n))
    let recursive_body = Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0));
    assert!(mentions_name(&recursive_body, &name));
}

#[test]
fn test_code_recursion_detection() {
    let target = Name::from_string("Nat.succ");
    let other = Name::from_string("Nat.zero");

    let mut id_gen = FVarIdGen::new();
    let fvar = id_gen.fresh();

    let non_recursive = Code::let_bind(
        LetDecl::new(
            fvar,
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::Const {
                name: other,
                levels: Vec::new(),
                args: Vec::new(),
            },
        ),
        Code::ret(fvar),
    );
    assert!(!code_mentions_name(&non_recursive, &target));

    let recursive = Code::let_bind(
        LetDecl::new(
            fvar,
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::Const {
                name: target.clone(),
                levels: Vec::new(),
                args: Vec::new(),
            },
        ),
        Code::ret(fvar),
    );
    assert!(code_mentions_name(&recursive, &target));
}

#[test]
fn test_code_recursion_detection_nested_fun() {
    let target = Name::from_string("Nat.succ");

    let mut id_gen = FVarIdGen::new();
    let outer_fvar = id_gen.fresh();
    let inner_fvar = id_gen.fresh();

    let inner_body = Code::let_bind(
        LetDecl::new(
            inner_fvar,
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::Const {
                name: target.clone(),
                levels: Vec::new(),
                args: Vec::new(),
            },
        ),
        Code::ret(inner_fvar),
    );

    let fun_decl = FunDecl::new(
        outer_fvar,
        Name::anon(),
        Vec::new(),
        Expr::const_str("Nat"),
        inner_body,
    );

    let code = Code::fun(fun_decl, Code::ret(outer_fvar));
    assert!(code_mentions_name(&code, &target));
}

#[test]
fn test_code_recursion_detection_ctor_value() {
    let target = Name::from_string("Nat.succ");

    let mut id_gen = FVarIdGen::new();
    let fvar = id_gen.fresh();

    let recursive = Code::let_bind(
        LetDecl::new(
            fvar,
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::Ctor {
                name: target.clone(),
                levels: Vec::new(),
                args: Vec::new(),
            },
        ),
        Code::ret(fvar),
    );

    assert!(code_mentions_name(&recursive, &target));
}

#[test]
fn test_code_recursion_detection_type_arg() {
    let target = Name::from_string("Nat.succ");
    let other = Name::from_string("Nat.add");

    let mut id_gen = FVarIdGen::new();
    let fvar = id_gen.fresh();

    let recursive = Code::let_bind(
        LetDecl::new(
            fvar,
            Name::anon(),
            Expr::const_str("Nat"),
            LetValue::Const {
                name: other,
                levels: Vec::new(),
                args: vec![Arg::Type(Expr::const_(target.clone(), Vec::new()))],
            },
        ),
        Code::ret(fvar),
    );

    assert!(code_mentions_name(&recursive, &target));
}

#[test]
fn test_code_recursion_detection_in_let_type() {
    let target = Name::from_string("Nat.succ");

    let mut id_gen = FVarIdGen::new();
    let fvar = id_gen.fresh();

    let recursive = Code::let_bind(
        LetDecl::new(
            fvar,
            Name::anon(),
            Expr::const_(target.clone(), Vec::new()),
            LetValue::Erased,
        ),
        Code::ret(fvar),
    );

    assert!(code_mentions_name(&recursive, &target));
}

#[test]
fn test_code_recursion_detection_cases_ctor_name() {
    let target = Name::from_string("Nat.succ");

    let mut id_gen = FVarIdGen::new();
    let scrutinee = id_gen.fresh();

    let code = Code::cases(
        Name::from_string("Nat"),
        Expr::const_str("Nat"),
        scrutinee,
        vec![Alt::ctor(target.clone(), Vec::new(), Code::ret(scrutinee))],
    );

    assert!(code_mentions_name(&code, &target));
}

#[test]
fn test_code_recursion_detection_cases_param_type() {
    let target = Name::from_string("Nat.succ");
    let other = Name::from_string("Nat.zero");

    let mut id_gen = FVarIdGen::new();
    let scrutinee = id_gen.fresh();
    let param = Param::new(
        id_gen.fresh(),
        Name::anon(),
        Expr::const_(target.clone(), Vec::new()),
    );

    let code = Code::cases(
        Name::from_string("Nat"),
        Expr::const_str("Nat"),
        scrutinee,
        vec![Alt::ctor(other, vec![param], Code::ret(scrutinee))],
    );

    assert!(code_mentions_name(&code, &target));
}

#[test]
fn test_code_recursion_detection_jmp_type_arg() {
    let target = Name::from_string("Nat.succ");

    let mut id_gen = FVarIdGen::new();
    let jp = id_gen.fresh();

    let code = Code::Jmp {
        jp,
        args: vec![Arg::Type(Expr::const_(target.clone(), Vec::new()))],
    };

    assert!(code_mentions_name(&code, &target));
}

// ========================================================================
// Erasure classification tests (Part of #1010)
// ========================================================================

#[test]
fn test_classify_expr_arg_infer_failure_is_normal() {
    // When type inference fails, classify_expr_arg should conservatively
    // return Normal (not erasable) to be safe.
    let env = make_env();

    // An unbound FVar cannot have its type inferred
    let unbound_fvar = Expr::fvar(FVarId::new(999));
    assert_eq!(classify_expr_arg(&env, &unbound_fvar), ExprArgClass::Normal);
    assert!(!is_erasable(&env, &unbound_fvar));
}

#[test]
fn test_classify_expr_arg_sprop_type() {
    // Expressions whose type is SProp should be classified as Erased
    let mut env = Environment::with_mode(clean_kernel::CleanMode::Impredicative);
    let sprop_name = add_axiom(&mut env, "MySProp", Expr::from_kind(ExprKind::SProp));
    let sprop_const = Expr::const_(sprop_name, Vec::<Level>::new());

    assert_eq!(classify_expr_arg(&env, &sprop_const), ExprArgClass::Erased);
    assert!(is_erasable(&env, &sprop_const));
}

#[test]
fn test_classify_expr_arg_raw_sprop() {
    // Raw SProp expression should be classified as Type (it's a Sort-like thing)
    let env = make_env();
    assert_eq!(
        classify_expr_arg(&env, &Expr::from_kind(ExprKind::SProp)),
        ExprArgClass::Type
    );
}

/// C5a: a Pi is ALWAYS a type — including an OPEN Pi (loose BVars from
/// stripped enclosing binders), where whole-term inference fails and the old
/// `Normal` fallback sent the Pi into the let-value catch-all as an
/// "Expression form: Pi(..)" error (the `BEq.beq` motive-body bucket).
#[test]
fn test_classify_expr_arg_open_pi_is_type() {
    let env = full_prelude_env();
    // `BVar(4) -> BVar(5) -> Bool` — the literal failing shape from BEq.beq.
    let open_pi = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(4),
        Expr::pi(BinderInfo::Default, Expr::bvar(5), Expr::const_str("Bool")),
    );
    assert_eq!(classify_expr_arg(&env, &open_pi), ExprArgClass::Type);
    assert!(is_erasable(&env, &open_pi));
}

/// C5a: a lambda whose peeled body is a TYPE is a type-level function (the
/// motive of a `<Ind>.rec` elimination, e.g. `fun _ => Bool`) and classifies
/// `Type` even when the lambda is open — while a lambda returning DATA stays
/// `Normal` (fail-closed: the erasure never widens to runtime values).
#[test]
fn test_classify_expr_arg_type_valued_lambda() {
    let env = full_prelude_env();

    // `fun (t : Decidable (BVar 0)) => Bool` — Decidable.decide's motive
    // shape: OPEN (the domain mentions a stripped binder), body a closed
    // type constant.
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::app(Expr::const_str("Decidable"), Expr::bvar(0)),
        Expr::const_str("Bool"),
    );
    assert_eq!(classify_expr_arg(&env, &motive), ExprArgClass::Type);

    // `fun (n : Nat) => n` returns data — must stay Normal.
    let id_nat = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
    assert_eq!(classify_expr_arg(&env, &id_nat), ExprArgClass::Normal);

    // `fun (n : Nat) => Nat.succ n` (open application body) — inference on
    // the body fails, the fail-closed fallback keeps it Normal.
    let succ = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
    );
    assert_eq!(classify_expr_arg(&env, &succ), ExprArgClass::Normal);
}

/// C5a: `generic_cases_on` recognizes saturated `<Ind>.rec` spines over
/// non-recursive inductives (casesOn modulo argument order) and declines the
/// shapes it cannot lower faithfully: recursors of RECURSIVE inductives
/// (List.rec — induction hypotheses), eta-reduced minors (a bare-variable
/// minor would misalign De Bruijn indices), and single-0-field constructors
/// (PUnit-likes need no tag dispatch).
#[test]
fn test_generic_cases_on_rec_recognition() {
    let env = full_prelude_env();

    // The real Decidable.decide body: strip its two lambdas and the peeled
    // body is a saturated `Decidable.rec` spine with lambda minors.
    let decide = env
        .get_const(&Name::from_string("Decidable.decide"))
        .unwrap();
    let mut body = decide.value.as_ref().unwrap();
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner.as_ref();
    }
    assert!(
        lower::generic_cases_on(&env, body).is_some(),
        "Decidable.rec (non-recursive, lambda minors) must be recognized"
    );

    // The real List.beq body eliminates via List.rec (recursive: the cons
    // rule carries an induction hypothesis) — must be declined.
    let list_beq = env.get_const(&Name::from_string("List.beq")).unwrap();
    let mut body = list_beq.value.as_ref().unwrap();
    while let ExprKind::Lam(_, _, inner) = body.kind() {
        body = inner.as_ref();
    }
    if let ExprKind::App(_, _) = body.kind() {
        let (head, _) = collect_app_args(body);
        if matches!(head.kind(), ExprKind::Const(n, _) if n.to_string() == "List.rec") {
            assert!(
                lower::generic_cases_on(&env, body).is_none(),
                "List.rec (recursive inductive) must be declined"
            );
        }
    }
}

// ========================================================================
// Arg handling tests (Part of #1010)
// ========================================================================

#[test]
fn test_expr_to_arg_fvar_direct() {
    // Direct FVar expressions should become Arg::FVar
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    let fvar_expr = Expr::fvar(FVarId::new(42));
    let arg = expr_to_arg(&mut ctx, &fvar_expr).unwrap();
    assert_eq!(arg, Arg::FVar(FVarId::new(42)));
}

#[test]
fn test_expr_to_arg_bvar_lookup() {
    // BVar expressions should look up in context and become Arg::FVar
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    // Push two binders to create a context
    let fv0 = ctx.push_binder();
    let fv1 = ctx.push_binder();

    // BVar(0) is innermost (fv1)
    let arg0 = expr_to_arg(&mut ctx, &Expr::bvar(0)).unwrap();
    assert_eq!(arg0, Arg::FVar(fv1));

    // BVar(1) is next (fv0)
    let arg1 = expr_to_arg(&mut ctx, &Expr::bvar(1)).unwrap();
    assert_eq!(arg1, Arg::FVar(fv0));
}

#[test]
fn test_expr_to_arg_bvar_unbound_error() {
    // Unbound BVar should produce an error
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    // No binders pushed, BVar(0) is unbound
    let err = expr_to_arg(&mut ctx, &Expr::bvar(0)).expect_err("unbound BVar(0) should fail");
    assert!(
        matches!(err, CompilerError::InvalidExpr(_)),
        "expected InvalidExpr, got: {err:?}"
    );
}

#[test]
fn test_expr_to_arg_complex_gets_let_bound() {
    // Complex expressions (not FVar/BVar/erased) should be let-bound
    // and return an Arg::FVar referencing the new binding
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    // A literal needs to be let-bound
    let lit_expr = Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
        clean_kernel::BigNat::Small(123),
    )));
    let arg = expr_to_arg(&mut ctx, &lit_expr).unwrap();

    // Should get an FVar (the let-binding target)
    assert!(matches!(arg, Arg::FVar(_)));

    // Context should have one let binding
    let lets = ctx.take_lets();
    assert_eq!(lets.len(), 1);
    assert!(matches!(
        &lets[0].value,
        LetValue::Lit(clean_kernel::Literal::Nat(n)) if n.to_u64() == Some(123)
    ));
}

#[test]
fn test_expr_to_arg_erased_for_prop() {
    // Prop-typed expressions should produce Arg::Erased
    let mut env = make_env();
    let prop_name = add_axiom(&mut env, "MyProp", Expr::prop());
    let prop_const = Expr::const_(prop_name, Vec::<Level>::new());

    let mut ctx = LcnfContext::new(&env);
    let arg = expr_to_arg(&mut ctx, &prop_const).unwrap();
    assert!(matches!(arg, Arg::Erased));
}

#[test]
fn test_expr_to_arg_type_for_type_expr() {
    // Type expressions should produce Arg::Type
    let mut env = make_env();
    let ty_name = add_axiom(&mut env, "MyType", Expr::type_());
    let ty_const = Expr::const_(ty_name.clone(), Vec::<Level>::new());

    let mut ctx = LcnfContext::new(&env);
    let arg = expr_to_arg(&mut ctx, &ty_const).unwrap();

    // Should be Arg::Type containing the expression
    match arg {
        Arg::Type(expr) => {
            assert!(matches!(expr.kind(), ExprKind::Const(name, _) if *name == ty_name));
        }
        _ => panic!("Expected Arg::Type, got {:?}", arg),
    }
}

#[test]
fn test_expr_to_arg_sort_is_type() {
    // Sort expressions should produce Arg::Type
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    let sort_expr = Expr::sort(Level::zero());
    let arg = expr_to_arg(&mut ctx, &sort_expr).unwrap();
    assert!(matches!(arg, Arg::Type(_)));
}

// ========================================================================
// Singleton type detection tests (Part of #1004)
// ========================================================================

/// Helper to register a Unit-like inductive type (one constructor, no fields)
fn register_unit_inductive(env: &mut Environment) -> Name {
    use clean_kernel::{ConstructorVal, InductiveVal};

    let unit_name = Name::from_string("MyUnit");
    let unit_star_name = Name::from_string("MyUnit.star");
    let unit_type = Expr::const_(unit_name.clone(), Vec::<Level>::new());

    // Register the inductive
    let ind_val = InductiveVal {
        name: unit_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![unit_name.clone()],
        constructor_names: vec![unit_star_name.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    // Register the constructor (star : MyUnit)
    let ctor_val = ConstructorVal {
        name: unit_star_name.clone(),
        inductive_name: unit_name.clone(),
        level_params: vec![],
        type_: unit_type.clone(),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    unit_name
}

/// Helper to register a Bool-like inductive type (two constructors, no fields)
fn register_bool_inductive(env: &mut Environment) -> Name {
    use clean_kernel::{ConstructorVal, InductiveVal};

    let bool_name = Name::from_string("MyBool");
    let true_name = Name::from_string("MyBool.true");
    let false_name = Name::from_string("MyBool.false");
    let bool_type = Expr::const_(bool_name.clone(), Vec::<Level>::new());

    // Register the inductive
    let ind_val = InductiveVal {
        name: bool_name.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![bool_name.clone()],
        constructor_names: vec![true_name.clone(), false_name.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    // Register constructors
    let true_ctor = ConstructorVal {
        name: true_name.clone(),
        inductive_name: bool_name.clone(),
        level_params: vec![],
        type_: bool_type.clone(),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    };
    env.register_constructor(true_ctor);

    let false_ctor = ConstructorVal {
        name: false_name.clone(),
        inductive_name: bool_name.clone(),
        level_params: vec![],
        type_: bool_type.clone(),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 1,
    };
    env.register_constructor(false_ctor);

    bool_name
}

/// Helper to register a Sigma-like inductive with a proof field
/// Sigma (A : Type) (P : A → Prop) := mk : (a : A) → P a → Sigma A P
fn register_subtype_inductive(env: &mut Environment) -> Name {
    use clean_kernel::{ConstructorVal, InductiveVal};

    let subtype_name = Name::from_string("MySigma");
    let mk_name = Name::from_string("MySigma.mk");

    // MySigma takes two parameters: (A : Type) and (P : A → Prop)
    // MySigma A P : Type
    // We'll simplify the type signature for testing

    // Type signature: (A : Type) → (A → Prop) → Type
    let type_param = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            Expr::arrow(Expr::bvar(0), Expr::prop()),
            Expr::type_(),
        ),
    );

    // Constructor type: (A : Type) → (P : A → Prop) → (a : A) → P a → MySigma A P
    // Simplified: this constructor has 2 params (A, P), and 2 fields (a : A, proof : P a)
    // For testing singleton detection, we want a type where the proof field is erasable

    let a_ty = Expr::type_();
    let p_ty = Expr::arrow(Expr::bvar(0), Expr::prop());
    let ctor_type = Expr::pi(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::pi(
            BinderInfo::Default,
            p_ty,
            Expr::pi(
                BinderInfo::Default,
                Expr::bvar(1), // a : A
                Expr::pi(
                    BinderInfo::Default,
                    Expr::app(Expr::bvar(2), Expr::bvar(0)), // P a : Prop
                    Expr::app(
                        Expr::app(Expr::const_(subtype_name.clone(), vec![]), Expr::bvar(3)),
                        Expr::bvar(2),
                    ),
                ),
            ),
        ),
    );

    let ind_val = InductiveVal {
        name: subtype_name.clone(),
        level_params: vec![],
        type_: type_param,
        num_params: 2,
        num_indices: 0,
        all_names: vec![subtype_name.clone()],
        constructor_names: vec![mk_name.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    };
    env.register_inductive(ind_val);

    let ctor_val = ConstructorVal {
        name: mk_name.clone(),
        inductive_name: subtype_name.clone(),
        level_params: vec![],
        type_: ctor_type,
        num_params: 2,
        num_fields: 2, // a and the proof
        constructor_idx: 0,
    };
    env.register_constructor(ctor_val);

    subtype_name
}

#[test]
fn test_is_singleton_unit() {
    // Unit-like types (one constructor, no fields) are singletons
    let mut env = make_env();
    let unit_name = register_unit_inductive(&mut env);
    let unit_type = Expr::const_(unit_name, Vec::<Level>::new());

    assert!(
        is_singleton_type(&env, &unit_type),
        "Unit (one constructor, no fields) should be singleton"
    );
}

#[test]
fn test_is_singleton_not_bool() {
    // Bool-like types (two constructors) are NOT singletons
    let mut env = make_env();
    let bool_name = register_bool_inductive(&mut env);
    let bool_type = Expr::const_(bool_name, Vec::<Level>::new());

    assert!(
        !is_singleton_type(&env, &bool_type),
        "Bool (two constructors) should NOT be singleton"
    );
}

#[test]
fn test_string_is_not_singleton() {
    let env = Environment::with_prelude();
    let string_type = Expr::const_str("String");

    assert!(
        !is_singleton_type(&env, &string_type),
        "String carries a runtime List Char payload and must not be singleton"
    );
}

#[test]
fn test_string_literal_arg_is_not_erased() {
    let env = Environment::with_prelude();
    let lit = Expr::str_lit("hi");

    assert_eq!(
        classify_expr_arg(&env, &lit),
        ExprArgClass::Normal,
        "String literals must remain runtime arguments"
    );
}

#[test]
fn test_is_singleton_non_inductive() {
    // Non-inductive types are not singletons
    let mut env = make_env();
    let axiom_name = add_axiom(&mut env, "SomeAxiom", Expr::type_());
    let axiom_type = Expr::const_(axiom_name, Vec::<Level>::new());

    assert!(
        !is_singleton_type(&env, &axiom_type),
        "Non-inductive types should NOT be singleton"
    );
}

#[test]
fn test_is_singleton_unknown_type() {
    // Unknown types are not singletons
    let env = make_env();
    let unknown_type = Expr::const_str("UnknownType");

    assert!(
        !is_singleton_type(&env, &unknown_type),
        "Unknown types should NOT be singleton"
    );
}

#[test]
fn test_is_singleton_applied_type() {
    // Test with applied types (e.g., List Nat)
    let mut env = make_env();
    let unit_name = register_unit_inductive(&mut env);

    // Apply unit to something (which doesn't make sense but tests head extraction)
    let applied = Expr::app(Expr::const_(unit_name, Vec::<Level>::new()), Expr::type_());

    // The head should be extracted correctly
    assert!(
        is_singleton_type(&env, &applied),
        "Applied singleton type should still be recognized"
    );
}

#[test]
fn test_classify_singleton_value_erased() {
    // Values of singleton types should be classified as Erased
    let mut env = make_env();
    let unit_name = register_unit_inductive(&mut env);
    let _unit_star_name = Name::from_string("MyUnit.star");

    // Add the star constant
    add_axiom(
        &mut env,
        "myUnitVal",
        Expr::const_(unit_name.clone(), Vec::<Level>::new()),
    );
    let val_expr = Expr::const_str("myUnitVal");

    assert_eq!(
        classify_expr_arg(&env, &val_expr),
        ExprArgClass::Erased,
        "Values of singleton types should be erased"
    );
}

#[test]
fn test_is_singleton_not_sigma() {
    // Sigma types with a non-erased field (the value field 'a') are NOT singletons
    let mut env = make_env();
    let sigma_name = register_subtype_inductive(&mut env);

    // Note: MySigma A P is not singleton because the field 'a : A' is not erasable
    // (A is a type parameter, the field itself is of type A which is not a proof)
    let sigma_type = Expr::app(
        Expr::app(
            Expr::const_(sigma_name, Vec::<Level>::new()),
            Expr::type_(), // A = Type
        ),
        Expr::bvar(0), // P (doesn't matter for this test)
    );

    // This should NOT be singleton because 'a : A' is not erasable when A = Type
    // Actually, checking is_singleton will fail because we can't determine if BVar(0)
    // (representing 'a') when applied to the subtype is erasable without more context.
    // This is expected - partial types are conservatively treated as non-singleton.
    assert!(
        !is_singleton_type(&env, &sigma_type),
        "Sigma with non-erased fields should NOT be singleton"
    );
}

// -- Bool conditional lowering (`cond` / `Bool.casesOn`) ---------------------

/// Apply `head` to `args` left-to-right, building a curried application.
fn apply_all(head: Expr, args: Vec<Expr>) -> Expr {
    args.into_iter().fold(head, Expr::app)
}

/// Extract the single `Cases` node from a lowered conditional body, walking
/// past any leading scrutinee let-bindings.
fn expect_cases(code: &Code) -> &crate::lcnf::Cases {
    let mut cur = code;
    loop {
        match cur {
            Code::Cases(c) => return c,
            Code::Let(_, rest) => cur = rest,
            other => panic!("expected Cases (optionally under lets), got {other:?}"),
        }
    }
}

#[test]
fn test_lower_cond_to_cases_over_bool() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    // cond α c t e  (α/c/t/e are opaque value constants → lower to FVars)
    let expr = apply_all(
        Expr::const_str("cond"),
        vec![
            Expr::const_str("alpha"),
            Expr::const_str("c"),
            Expr::const_str("t"),
            Expr::const_str("e"),
        ],
    );

    let code = expr_to_code(&mut ctx, &expr).expect("cond should lower");
    let cases = expect_cases(&code);

    assert_eq!(cases.type_name, Name::from_string("Bool"));
    assert_eq!(cases.alts.len(), 2);
    // Alternatives are emitted in constructor-tag order: false first, true second.
    match (&cases.alts[0], &cases.alts[1]) {
        (
            Alt::Ctor {
                ctor_name: c0,
                params: p0,
                ..
            },
            Alt::Ctor {
                ctor_name: c1,
                params: p1,
                ..
            },
        ) => {
            assert_eq!(c0, &Name::from_string("Bool.false"));
            assert_eq!(c1, &Name::from_string("Bool.true"));
            assert!(p0.is_empty() && p1.is_empty(), "Bool ctors take no fields");
        }
        other => panic!("expected two Ctor alts, got {other:?}"),
    }
}

#[test]
fn test_lower_cond_branches_return_distinct_values() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let expr = apply_all(
        Expr::const_str("cond"),
        vec![
            Expr::const_str("alpha"),
            Expr::const_str("c"),
            Expr::const_str("then_val"),
            Expr::const_str("else_val"),
        ],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("cond should lower");
    let cases = expect_cases(&code);

    // false branch is `else_val`, true branch is `then_val`; both bodies are a
    // (let-wrapped) Return of their own fvar — and the two fvars differ.
    let false_ret = terminal_return_fvar(cases.alts[0].body());
    let true_ret = terminal_return_fvar(cases.alts[1].body());
    assert_ne!(
        false_ret, true_ret,
        "the two branches must bind/return distinct values"
    );
}

#[test]
fn test_lower_bool_caseson_swaps_branch_order() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    // Bool.casesOn motive c false_case true_case
    // Lean lists the false alternative first; our lowering must still place
    // `Bool.false => false_case` and `Bool.true => true_case`.
    let expr = apply_all(
        Expr::const_str("Bool.casesOn"),
        vec![
            Expr::const_str("motive"),
            Expr::const_str("c"),
            Expr::const_str("false_case"),
            Expr::const_str("true_case"),
        ],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("Bool.casesOn should lower");
    let cases = expect_cases(&code);
    assert_eq!(cases.alts.len(), 2);
    match &cases.alts[0] {
        Alt::Ctor { ctor_name, .. } => {
            assert_eq!(ctor_name, &Name::from_string("Bool.false"))
        }
        other => panic!("expected Bool.false alt first, got {other:?}"),
    }
}

#[test]
fn test_non_bool_cond_application_not_lowered_to_cases() {
    // A regular constant application is unaffected: it stays a Return of a
    // let-bound constant, never a `Cases`.
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let expr = apply_all(
        Expr::const_str("Nat.add"),
        vec![Expr::const_str("x"), Expr::const_str("y")],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("Nat.add should lower");
    assert!(
        !matches!(strip_lets(&code), Code::Cases(_)),
        "ordinary application must not become a Cases, got {code:?}"
    );
}

/// Return the fvar of a terminal `Return`, walking past leading lets.
fn terminal_return_fvar(code: &Code) -> FVarId {
    match strip_lets(code) {
        Code::Return(fv) => *fv,
        other => panic!("expected a Return terminal, got {other:?}"),
    }
}

// -- `if` / `match` recursor lowering (`Bool.rec` / `Nat.casesOn`) ------------

#[test]
fn test_lower_bool_rec_to_cases_with_motive_erased() {
    // The spine the elaborator emits for `if b then x else y`:
    //   Bool.rec motive minor_false minor_true b
    // The motive (arg0) is type-level and must be dropped; the scrutinee is the
    // LAST argument; the minor premises are in ctor-tag order (false, true).
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let expr = apply_all(
        Expr::const_str("Bool.rec"),
        vec![
            Expr::const_str("motive"),
            Expr::const_str("else_val"),
            Expr::const_str("then_val"),
            Expr::const_str("b"),
        ],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("Bool.rec should lower to Cases");
    let cases = expect_cases(&code);

    assert_eq!(cases.type_name, Name::from_string("Bool"));
    assert_eq!(cases.alts.len(), 2);
    match (&cases.alts[0], &cases.alts[1]) {
        (Alt::Ctor { ctor_name: c0, .. }, Alt::Ctor { ctor_name: c1, .. }) => {
            assert_eq!(c0, &Name::from_string("Bool.false"));
            assert_eq!(c1, &Name::from_string("Bool.true"));
        }
        other => panic!("expected two Ctor alts, got {other:?}"),
    }
    // The two branches return distinct (let-bound) values — real selection.
    let false_ret = terminal_return_fvar(cases.alts[0].body());
    let true_ret = terminal_return_fvar(cases.alts[1].body());
    assert_ne!(false_ret, true_ret);
}

#[test]
fn test_lower_nat_caseson_to_cases_zero_ctor_plus_succ_default() {
    // The spine for `match n with | 0 => z | _ => s`:
    //   Nat.casesOn motive n zero_branch (fun pred => succ_body)
    // We lower to a `Cases` over `Nat` with `Nat.zero` as an exact ctor alt
    // (tag 0) and the successor case as the `Default` arm (every k >= 1).
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let succ_lambda = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::const_str("succ_val"),
    );
    let expr = apply_all(
        Expr::const_str("Nat.casesOn"),
        vec![
            Expr::const_str("motive"),
            Expr::const_str("n"),
            Expr::const_str("zero_val"),
            succ_lambda,
        ],
    );
    let code = expr_to_code(&mut ctx, &expr).expect("Nat.casesOn should lower to Cases");
    let cases = expect_cases(&code);

    assert_eq!(cases.type_name, Name::from_string("Nat"));
    assert_eq!(cases.alts.len(), 2);
    match &cases.alts[0] {
        Alt::Ctor { ctor_name, .. } => {
            assert_eq!(ctor_name, &Name::from_string("Nat.zero"))
        }
        other => panic!("expected Nat.zero ctor alt first, got {other:?}"),
    }
    assert!(
        matches!(&cases.alts[1], Alt::Default(_)),
        "successor case must be the Default arm, got {:?}",
        cases.alts[1]
    );
}

#[test]
fn test_nat_rec_routes_through_synthesized_recursion_not_enclosing_self_call() {
    // Structural recursion `def fact | 0 => 1 | n+1 => (n+1) * fact n`
    // elaborates to:
    //   Nat.rec motive 1 (fun pred ih => (pred+1) * ih) n
    //
    // This USED to be lowered by a dedicated arm that materialized the
    // induction hypothesis as `fact(pred)` — the ENCLOSING declaration
    // applied to the predecessor ONLY. That special case is retired (it
    // under-applied every multi-parameter declaration; see the multi-param
    // pin below): the spine now routes through the R1 synthesized-recursion
    // path, which emits a local `go` whose IH is a self-call to GO.
    //
    // Needs the real prelude: `rec_apply_parts` recognizes `Nat.rec` via the
    // registered kernel recursor (metadata), not by name.
    let env = Environment::with_prelude();
    let mut ctx = LcnfContext::new(&env);

    // succ minor: fun (pred : Nat) (ih : Nat) => Nat.mul (BVar 1) (BVar 0)
    let inner_body = apply_all(
        Expr::const_str("Nat.mul"),
        vec![Expr::bvar(1), Expr::bvar(0)],
    );
    let succ_lambda = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), inner_body),
    );
    // Nat.rec order (MajorAfterMinors): motive, zero, succ, major.
    let expr = apply_all(
        Expr::const_str("Nat.rec"),
        vec![
            Expr::const_str("motive"),
            Expr::from_kind(ExprKind::Lit(clean_kernel::Literal::Nat(
                clean_kernel::BigNat::Small(1),
            ))),
            succ_lambda,
            Expr::const_str("n"),
        ],
    );

    let code = expr_to_code(&mut ctx, &expr).expect("Nat.rec lowers via the R1 path");

    // The lowered value declares exactly one synthesized local function.
    fn find_fun(code: &Code) -> Option<&FunDecl> {
        match code {
            Code::Fun(decl, _) => Some(decl),
            Code::Let(_, rest) | Code::JoinPoint(_, rest) => find_fun(rest),
            _ => None,
        }
    }
    let go = find_fun(&code).expect("Nat.rec lowering synthesizes a local go");
    assert_eq!(
        go.params.len(),
        1,
        "inline-minor Nat.rec go takes only the scrutinee"
    );

    let Code::Cases(cases) = go.body.as_ref() else {
        panic!("go body must be a Cases over Nat, got {:?}", go.body);
    };
    assert_eq!(cases.type_name, Name::from_string("Nat"));
    assert_eq!(cases.alts.len(), 2);
    match &cases.alts[0] {
        Alt::Ctor { ctor_name, .. } => assert_eq!(ctor_name, &Name::from_string("Nat.zero")),
        other => panic!("expected Nat.zero ctor alt first, got {other:?}"),
    }
    let default_body = match &cases.alts[1] {
        Alt::Default(body) => body.as_ref(),
        other => panic!("successor case must be the Default arm, got {other:?}"),
    };

    // Successor arm: `pred := Nat.sub n 1`, and the IH is a SELF-CALL TO GO
    // (an FVar call on go's own id) — never a `Const` call back to any
    // enclosing declaration.
    let mut saw_sub = false;
    let mut saw_go_self_call = false;
    let mut cur = default_body;
    while let Code::Let(decl, rest) = cur {
        match &decl.value {
            LetValue::Const { name, .. } if name == &Name::from_string("Nat.sub") => {
                saw_sub = true;
            }
            LetValue::FVar { fvar, args } if *fvar == go.fvar_id => {
                assert_eq!(args.len(), 1, "go self-call passes exactly the predecessor");
                saw_go_self_call = true;
            }
            _ => {}
        }
        cur = rest;
    }
    assert!(saw_sub, "successor arm must bind pred := Nat.sub n 1");
    assert!(
        saw_go_self_call,
        "successor arm must materialize ih as a self-call to the synthesized go"
    );
}

#[test]
fn test_multi_param_nat_rec_never_self_calls_enclosing_decl() {
    // THE List.replicate CLASS (the retired arm's behavioral miscompile): a
    // MULTI-PARAMETER declaration recursing over `Nat`,
    //
    //   def myrep : Nat -> A -> B := fun n x =>
    //     Nat.rec motive (mkNil x) (fun pred ih => mkCons x ih) n
    //
    // The old dedicated arm materialized `ih := myrep(pred)` — the enclosing
    // declaration UNDER-APPLIED (missing `x`), handing the minor a PAP
    // closure instead of the recursive value. Pin the fix: the lowered body
    // must contain NO `Const("myrep", ..)` call at all; the IH must be a
    // self-call to the synthesized local go (whose captured `x` is threaded
    // by lambda lifting downstream).
    let env = Environment::with_prelude();

    let succ_lambda = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::lam(
            BinderInfo::Default,
            Expr::const_str("_"),
            // mkCons x ih — mentions the OUTER param x (BVar 3 here: under
            // pred+ih inside fun n x => .., x is BVar 2 + 0 minor depth.. use
            // the outer binder explicitly: [pred=BVar1, ih=BVar0, x=BVar2].
            apply_all(
                Expr::const_str("mkCons"),
                vec![Expr::bvar(2), Expr::bvar(0)],
            ),
        ),
    );
    let body = apply_all(
        Expr::const_str("Nat.rec"),
        vec![
            Expr::const_str("motive"),
            apply_all(Expr::const_str("mkNil"), vec![Expr::bvar(0)]),
            succ_lambda,
            Expr::bvar(1), // n
        ],
    );
    let value = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("Nat"),
        Expr::lam(BinderInfo::Default, Expr::const_str("_"), body),
    );
    let info = clean_kernel::ConstantInfo::new(
        Name::from_string("myrep"),
        vec![],
        Expr::const_str("_"),
        Some(value),
        false,
    );

    let decl = constant_to_decl(&env, &info)
        .expect("myrep lowers")
        .expect("myrep is computable");
    let crate::lcnf::DeclValue::Code(code) = &decl.body else {
        panic!("myrep lowers to code");
    };

    // Walk the WHOLE lowered body: no Const call to `myrep` anywhere (the
    // under-applied PAP-as-IH shape), and the synthesized go self-call exists.
    fn walk(code: &Code, myrep: &Name, saw_self_const: &mut bool, go_calls: &mut usize) {
        match code {
            Code::Let(decl, rest) => {
                if let LetValue::Const { name, .. } = &decl.value {
                    if name == myrep {
                        *saw_self_const = true;
                    }
                }
                walk(rest, myrep, saw_self_const, go_calls);
            }
            Code::Fun(fun, rest) | Code::JoinPoint(fun, rest) => {
                // Count FVar self-calls to this fun inside its own body.
                fn count_fvar_calls(code: &Code, target: FVarId, n: &mut usize) {
                    match code {
                        Code::Let(decl, rest) => {
                            if let LetValue::FVar { fvar, .. } = &decl.value {
                                if *fvar == target {
                                    *n += 1;
                                }
                            }
                            count_fvar_calls(rest, target, n);
                        }
                        Code::Fun(f, rest) | Code::JoinPoint(f, rest) => {
                            count_fvar_calls(&f.body, target, n);
                            count_fvar_calls(rest, target, n);
                        }
                        Code::Cases(cases) => {
                            for alt in &cases.alts {
                                count_fvar_calls(alt.body(), target, n);
                            }
                        }
                        _ => {}
                    }
                }
                count_fvar_calls(&fun.body, fun.fvar_id, go_calls);
                walk(&fun.body, myrep, saw_self_const, go_calls);
                walk(rest, myrep, saw_self_const, go_calls);
            }
            Code::Cases(cases) => {
                for alt in &cases.alts {
                    walk(alt.body(), myrep, saw_self_const, go_calls);
                }
            }
            _ => {}
        }
    }
    let mut saw_self_const = false;
    let mut go_self_calls = 0usize;
    walk(
        code,
        &Name::from_string("myrep"),
        &mut saw_self_const,
        &mut go_self_calls,
    );

    assert!(
        !saw_self_const,
        "multi-param Nat.rec must NOT self-call the enclosing decl (the \
         under-applied PAP-as-IH miscompile): {decl}"
    );
    assert!(
        go_self_calls >= 1,
        "the synthesized go must self-call for the IH: {decl}"
    );
}

/// Walk past leading `Let`/`Fun` wrappers to the inner control node.
fn strip_lets(code: &Code) -> &Code {
    let mut cur = code;
    loop {
        match cur {
            Code::Let(_, rest) | Code::Fun(_, rest) => cur = rest,
            other => return other,
        }
    }
}

// -- Generic `<Ind>.casesOn` lowering (Option/List-shaped matches) -----------

/// Register an `Option`-shaped inductive `MyOpt` (num_params = 0 for test
/// simplicity) with `MyOpt.none` (tag 0, 0 fields) and `MyOpt.some : Nat ->
/// MyOpt` (tag 1, 1 field).
fn register_myopt_inductive(env: &mut Environment) -> Name {
    use clean_kernel::{ConstructorVal, InductiveVal};

    let ind = Name::from_string("MyOpt");
    let none = Name::from_string("MyOpt.none");
    let some = Name::from_string("MyOpt.some");
    let ind_ty = Expr::const_(ind.clone(), Vec::<Level>::new());

    env.register_inductive(InductiveVal {
        name: ind.clone(),
        level_params: vec![],
        type_: Expr::type_(),
        num_params: 0,
        num_indices: 0,
        all_names: vec![ind.clone()],
        constructor_names: vec![none.clone(), some.clone()],
        is_recursive: false,
        is_reflexive: false,
        is_large_elim: true,
        is_nested: false,
    });

    env.register_constructor(ConstructorVal {
        name: none.clone(),
        inductive_name: ind.clone(),
        level_params: vec![],
        type_: ind_ty.clone(),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    });

    // some : Nat -> MyOpt
    env.register_constructor(ConstructorVal {
        name: some,
        inductive_name: ind.clone(),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, Expr::const_str("Nat"), ind_ty),
        num_params: 0,
        num_fields: 1,
        constructor_idx: 1,
    });

    ind
}

#[test]
fn test_lower_generic_cases_on_binds_fields_per_ctor() {
    let mut env = make_env();
    register_myopt_inductive(&mut env);
    let mut ctx = LcnfContext::new(&env);

    // MyOpt.casesOn (motive) (major = MyOpt.some 5) (none_minor = 0)
    //               (some_minor = fun (x : Nat) => x)
    //
    // Layout for a non-parametric, non-indexed inductive:
    //   [motive] [major] [minor_none] [minor_some]
    let major = Expr::app(Expr::const_str("MyOpt.some"), Expr::nat_lit(5));
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::const_str("MyOpt"),
        Expr::const_str("Nat"),
    );
    let none_minor = Expr::nat_lit(0);
    let some_minor = Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0));
    let expr = apply_all(
        Expr::const_str("MyOpt.casesOn"),
        vec![motive, major, none_minor, some_minor],
    );

    let code = expr_to_code(&mut ctx, &expr).expect("generic casesOn should lower");
    let cases = expect_cases(&code);

    assert_eq!(
        cases.type_name,
        Name::from_string("MyOpt"),
        "Cases type_name must be the inductive, driving ToMono dispatch"
    );
    assert_eq!(cases.alts.len(), 2, "one alt per constructor");

    // Alt order is constructor-tag order: none (0 fields), some (1 field).
    match &cases.alts[0] {
        Alt::Ctor {
            ctor_name, params, ..
        } => {
            assert_eq!(ctor_name, &Name::from_string("MyOpt.none"));
            assert!(params.is_empty(), "none binds no fields");
        }
        other => panic!("expected MyOpt.none ctor alt, got {other:?}"),
    }
    match &cases.alts[1] {
        Alt::Ctor {
            ctor_name, body, ..
        } => {
            assert_eq!(ctor_name, &Name::from_string("MyOpt.some"));
            // The some body must read the field via a projection let keyed by the
            // constructor name, then return it.
            let mut cur = body.as_ref();
            let mut saw_proj = false;
            while let Code::Let(decl, rest) = cur {
                if let LetValue::Proj { type_name, idx, .. } = &decl.value {
                    assert_eq!(type_name, &Name::from_string("MyOpt.some"));
                    assert_eq!(*idx, 0, "the single `some` field is at index 0");
                    saw_proj = true;
                }
                cur = rest.as_ref();
            }
            assert!(
                saw_proj,
                "some arm must project field 0 (the bound payload) off the scrutinee"
            );
        }
        other => panic!("expected MyOpt.some ctor alt, got {other:?}"),
    }
}

#[test]
fn test_generic_cases_on_declines_nat_cases() {
    // A `Nat.casesOn`-shaped spine is handled by `nat_cases_branches`, not the
    // generic arm; confirm `generic_cases_on` declines a `Nat.casesOn` head so
    // Nat keeps its boxed-integer lowering.
    let env = make_env();
    let nat_cases = apply_all(
        Expr::const_str("Nat.casesOn"),
        vec![
            Expr::const_str("motive"),
            Expr::const_str("n"),
            Expr::nat_lit(0),
            Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0)),
        ],
    );
    assert!(
        lower::generic_cases_on(&env, &nat_cases).is_none(),
        "generic recognizer must decline Nat.casesOn"
    );
}

// ---------------------------------------------------------------------------
// C3: type-level machinery erasure + `constant_to_decl` totality (no panics)
// ---------------------------------------------------------------------------

/// Full prelude environment (with IO ops), as the CLI probes see it.
fn full_prelude_env() -> Environment {
    let mut env = Environment::with_prelude();
    let _ = env.init_io_ops();
    env
}

/// Lower one named prelude constant through `constant_to_decl`.
fn lower_named(env: &Environment, name: &str) -> Result<Option<crate::lcnf::Decl>, CompilerError> {
    let info = env
        .get_const(&Name::from_string(name))
        .unwrap_or_else(|| panic!("{name} not in prelude"))
        .clone();
    constant_to_decl(env, &info)
}

/// C3 hardening: `constant_to_decl` must be total — a structured
/// `Ok(Some)/Ok(None)/Err` for EVERY prelude constant, panics on none of
/// them. (Before C3, 77 prelude definitions tripped the pending-scope
/// `debug_assert` in `LcnfContext::restore_pending` on branch-lowering
/// error paths.) Any panic fails this test directly.
#[test]
fn test_constant_to_decl_is_total_over_prelude() {
    let env = full_prelude_env();
    let names: Vec<Name> = env.constants().map(|c| c.name.clone()).collect();
    assert!(
        names.len() > 1500,
        "prelude unexpectedly small: {}",
        names.len()
    );
    for name in names {
        let info = env.get_const(&name).unwrap().clone();
        let _ = constant_to_decl(&env, &info);
    }
}

/// The `noConfusion` eliminator family is proof/type-level machinery with no
/// runtime content. `Add.noConfusionType` used to PANIC, then dropped via the
/// structured `Ok(None)` convention; it (and every other noConfusionType whose
/// body does not lower) now emits a faithful erased-returning stub
/// `let r := ⟨erased⟩; return r` so it lowers and emits end-to-end (census-OK)
/// instead of only being extern-referenced. Erasing a `Sort`-codomain
/// definition to the erased token is exactly Lean's own compiler erasure.
///
/// `Add.noConfusion` itself LOWERS from source since C5a (its `Eq.rec`
/// elimination spine now classifies its type-level motive correctly), so it
/// takes the normal path, not the erased-stub fallback.
#[test]
fn test_noconfusion_family_emits_erased_stub() {
    let env = full_prelude_env();
    for name in ["Add.noConfusionType", "Bool.noConfusionType"] {
        let decl = lower_named(&env, name)
            .unwrap_or_else(|e| panic!("{name}: stage-1 must lower, got {e:?}"))
            .unwrap_or_else(|| panic!("{name} must emit an erased stub, not drop to extern"));
        let crate::lcnf::DeclValue::Code(code) = &decl.body else {
            panic!("{name}: expected a Code body");
        };
        let Code::Let(let_decl, rest) = code.as_ref() else {
            panic!("{name}: expected `let _ := ⟨erased⟩; ..`, got {code:?}");
        };
        assert!(
            matches!(let_decl.value, LetValue::Erased),
            "{name}: the stub must bind the erased token, got {:?}",
            let_decl.value
        );
        assert!(
            matches!(rest.as_ref(), Code::Return(fv) if *fv == let_decl.fvar_id),
            "{name}: the stub must return its erased binding"
        );
    }
    assert!(
        matches!(lower_named(&env, "Add.noConfusion"), Ok(Some(_))),
        "Add.noConfusion lowers from source since C5a and must keep doing so"
    );
}

/// C5a review hardening: the noConfusion arm of `is_type_level_machinery` is
/// no longer name-only — a USER definition that merely names itself
/// `*.noConfusion` but returns DATA (here `Nat -> Nat`) must NEVER be dropped
/// to `Ok(None)` when its body fails to lower; silent erasure of a
/// data-returning definition would be miscompilation. It keeps a structured
/// error instead.
#[test]
fn test_user_data_returning_noconfusion_is_never_dropped() {
    let env = full_prelude_env();
    let nat = Expr::const_str("Nat");
    // Body: `fun (n : Nat) => <unbound BVar 5>` — well-shaped enough to reach
    // body lowering, guaranteed to FAIL it (unbound variable).
    let bad_body = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(5));
    let info = clean_kernel::ConstantInfo::new(
        Name::from_string("Weird.noConfusion"),
        vec![],
        Expr::pi(BinderInfo::Default, nat.clone(), nat),
        Some(bad_body),
        true,
    );
    assert!(
        constant_to_decl(&env, &info).is_err(),
        "a data-returning def named *.noConfusion must keep its lowering error"
    );
}

/// `Prop`-valued class heads (`LE.le : .. -> Prop` etc.) return a type; when
/// their type-level body does not lower they are no longer dropped to extern —
/// they emit a faithful erased-returning stub `let r := ⟨erased⟩; return r`.
/// The declared type's telescope-codomain is a `Sort`/`SProp` (proved by
/// `is_type_level_machinery`), so erasing the whole body to the erased token is
/// exactly Lean's own compiler erasure — never a miscompilation of runtime
/// data. This lets the head lower and emit end-to-end (census-OK) instead of
/// only ever being extern-referenced.
#[test]
fn test_prop_valued_class_heads_emit_erased_stub() {
    let env = full_prelude_env();
    for name in ["LE.le", "LT.lt", "Membership.mem"] {
        let decl = lower_named(&env, name)
            .unwrap_or_else(|e| panic!("{name}: stage-1 must lower, got {e:?}"))
            .unwrap_or_else(|| {
                panic!(
                    "{name} returns a type/Prop and must emit an erased stub, not drop to extern"
                )
            });
        let crate::lcnf::DeclValue::Code(code) = &decl.body else {
            panic!("{name}: expected a Code body");
        };
        let Code::Let(let_decl, rest) = code.as_ref() else {
            panic!("{name}: expected `let _ := ⟨erased⟩; ..`, got {code:?}");
        };
        assert!(
            matches!(let_decl.value, LetValue::Erased),
            "{name}: the stub must bind the erased token, got {:?}",
            let_decl.value
        );
        assert!(
            matches!(rest.as_ref(), Code::Return(fv) if *fv == let_decl.fvar_id),
            "{name}: the stub must return its erased binding"
        );
    }
}

/// A SINGLE-constructor Prop eliminator that does NOT large-eliminate
/// (`Int.NonNeg` — its `Nat` field is data, so the kernel forbids large
/// elimination and the motive is `… → Prop`) is a proof VALUE with unit
/// computational content. Its body references the valueless kernel recursor
/// `Int.NonNeg.rec`, which otherwise survives to the final IR and trips the
/// stage-2 valueless-recursor guard (the 2 census stage-2 residue roots).
/// `prop_multi_ctor_elim` now recognizes it and erases the whole elimination
/// to the faithful erased stub `let r := ⟨erased⟩; return r`, so it lowers and
/// emits end-to-end. Sound: a small-eliminating Prop produces only proofs.
#[test]
fn test_single_ctor_small_elim_prop_eliminator_emits_erased_stub() {
    let env = full_prelude_env();
    for name in ["Int.NonNeg.casesOn", "Int.NonNeg.recOn"] {
        let decl = lower_named(&env, name)
            .unwrap_or_else(|e| panic!("{name}: stage-1 must lower, got {e:?}"))
            .unwrap_or_else(|| {
                panic!("{name}: a single-ctor small-elim Prop eliminator must erase, not drop")
            });
        let crate::lcnf::DeclValue::Code(code) = &decl.body else {
            panic!("{name}: expected a Code body");
        };
        let Code::Let(let_decl, rest) = code.as_ref() else {
            panic!("{name}: expected `let _ := ⟨erased⟩; ..`, got {code:?}");
        };
        assert!(
            matches!(let_decl.value, LetValue::Erased),
            "{name}: the stub must bind the erased token, got {:?}",
            let_decl.value
        );
        assert!(
            matches!(rest.as_ref(), Code::Return(fv) if *fv == let_decl.fvar_id),
            "{name}: the stub must return its erased binding"
        );
    }
}

/// FAIL-CLOSED GUARD: a single-constructor Prop that DOES large-eliminate
/// (`Eq`/`Acc`/`And` — subsingleton elimination carries runtime content:
/// `Eq.rec` casts, `Acc.rec` well-founded recursion) is deliberately NOT
/// erased by the extended `prop_multi_ctor_elim`; it keeps its real lowering.
/// The `is_large_elim` gate is what separates these from `Int.NonNeg`.
#[test]
fn test_single_ctor_large_elim_prop_eliminator_not_erased() {
    let env = full_prelude_env();
    for name in ["Eq.casesOn", "Acc.casesOn", "And.casesOn"] {
        // Whatever they lower to (real Code from source, or a structured
        // drop/error), it must NOT be the bare erased-return stub.
        if let Ok(Some(decl)) = lower_named(&env, name) {
            if let crate::lcnf::DeclValue::Code(code) = &decl.body {
                let is_bare_erased_stub = matches!(
                    code.as_ref(),
                    Code::Let(let_decl, rest)
                        if matches!(let_decl.value, LetValue::Erased)
                        && matches!(rest.as_ref(), Code::Return(fv) if *fv == let_decl.fvar_id)
                );
                assert!(
                    !is_bare_erased_stub,
                    "{name}: a large-eliminating subsingleton must NOT erase to the unit stub"
                );
            }
        }
    }
}

/// CORRECTNESS GUARD, strengthened by C5a: a computable definition that
/// returns DATA must never be silently erased — and since the open-term
/// classification fix these `<Ind>.rec`-spelled heads now LOWER from source
/// (their type-level motive lambdas classify `Type`, the non-recursive
/// eliminations lower as `Cases`). `Ok(Some)` is strictly stronger than the
/// pre-C5a pin (a structured `Err`); `Ok(None)` remains the miscompilation
/// this test exists to forbid.
///
/// C5a bucket pins, 3 per census bucket:
/// * "Cannot return a type" (motive body is a closed type constant):
///   `Decidable.decide`, `Fin.val`, `Int.add`;
/// * "other expression form: Pi(..)" (motive body is an OPEN Pi):
///   `BEq.beq`, `Hashable.hash`, `Iff.mp`.
#[test]
fn test_data_returning_defs_never_silently_erased() {
    let env = full_prelude_env();
    for name in [
        // bucket: "Cannot return a type"
        "Decidable.decide",
        "Fin.val",
        "Int.add",
        // bucket: "other expression form" (open Pi motive body)
        "BEq.beq",
        "Hashable.hash",
        "Iff.mp",
    ] {
        assert!(
            matches!(lower_named(&env, name), Ok(Some(_))),
            "{name} returns data and lowers from source since C5a \
             (and must NEVER be Ok(None))"
        );
    }
}

/// RUNG B graduation: WELL-FOUNDED recursion now lowers from source.
///
/// `WellFounded.fix` was the pinned stage-1 survivor — `Acc.rec`-backed
/// recursion is NOT structural (`Acc` is reflexive: its recursive field is
/// function-typed and its major premise is an erased `Prop` proof), so the
/// R1 synthesized-eliminator path (`rec_apply_parts`) deliberately declines
/// it, and its body's erased accessibility proof (a `Proj`-headed application)
/// crashed stage-1 outright.
///
/// The RUNG-B recognizer (`wf_rec_apply_parts` / `lower_wf_rec_apply`) now
/// synthesizes a value-recursive `go` — `go step v hr = step v [box0] (go
/// step)` — recursing on the recovered INDEX value, never on the erased `Acc`
/// scrutinee. So `WellFounded.fix`, `WellFounded.fixF`, `Acc.recOn`, and
/// `Acc.casesOn` all lower `Ok(Some)` from source (the same strictly-stronger
/// upgrade `Nat.recOn` took with R1), behavior-verified leak-free and ASan-
/// clean by the emit_c well-founded differential.
#[test]
fn test_well_founded_recursion_lowers_from_source() {
    let env = full_prelude_env();
    for name in [
        "WellFounded.fix",
        "WellFounded.fixF",
        "Acc.recOn",
        "Acc.casesOn",
    ] {
        assert!(
            matches!(lower_named(&env, name), Ok(Some(_))),
            "{name} is well-founded (Acc.rec-backed) and lowers from source \
             via the RUNG-B value-recursive synthesis (never Ok(None), never \
             a structured error)"
        );
    }
}

/// The erasure fallback fires only when lowering FAILS: a Sort-codomain
/// declaration whose body lowers fine keeps compiling from source
/// (`Empty.noConfusionType` is in the end-to-end OK set), and ordinary data
/// definitions are untouched.
#[test]
fn test_type_level_decl_that_lowers_stays_compiled() {
    let env = full_prelude_env();
    assert!(
        matches!(lower_named(&env, "Empty.noConfusionType"), Ok(Some(_))),
        "Empty.noConfusionType lowers today and must keep doing so"
    );
    assert!(
        matches!(lower_named(&env, "Bool.not"), Ok(Some(_))),
        "ordinary data def must still compile from source"
    );
}

/// The `Char.decEq` shape (a branch-lowering path with pending lets queued)
/// was the panic class fixed by `LcnfContext::abandon_pending`, and pre-C5a
/// it pinned a structured error. Since C5a its `Char.rec` elimination lowers
/// as a `Cases`, so the strictly stronger `Ok(Some)` is pinned; the original
/// no-panic property is still exercised (any panic fails the test).
#[test]
fn test_failed_branch_lowering_returns_error_not_panic() {
    let env = full_prelude_env();
    assert!(
        matches!(lower_named(&env, "Char.decEq"), Ok(Some(_))),
        "Char.decEq (returns Decidable — data) lowers from source since C5a"
    );
}

// ---------------------------------------------------------------------------
// R1: recursive eliminators compiled from source (synthesized recursion)
// ---------------------------------------------------------------------------

/// R1 recognition: saturated `<Ind>.rec` spines over RECURSIVE single-motive,
/// non-indexed inductives are recognized by `rec_apply_parts` (which the
/// value-position `App` lowering funnels into `lower_rec_apply`), and every
/// out-of-scope shape declines fail-closed:
///
/// * `Acc.rec` — REFLEXIVE (function-typed recursive field): recursion on it
///   is well-founded, NOT structural. Must refuse.
/// * `Eq.rec` / `HEq.rec` — indexed families. Must refuse.
/// * partial applications (minors missing). Must refuse.
#[test]
fn test_r1_rec_apply_parts_recognition_and_refusals() {
    let env = full_prelude_env();
    let peeled = |name: &str| {
        let info = env.get_const(&Name::from_string(name)).unwrap();
        let mut body = info.value.as_ref().unwrap();
        while let ExprKind::Lam(_, _, inner) = body.kind() {
            body = inner.as_ref();
        }
        body.clone()
    };

    // List.length: `List.rec` over a RECURSIVE inductive, saturated.
    assert!(
        lower::rec_apply_parts(&env, &peeled("List.length")).is_some(),
        "saturated List.rec (recursive, direct self-field) must be recognized"
    );
    // List.foldl: function-building motive — the spine is OVER-applied.
    assert!(
        lower::rec_apply_parts(&env, &peeled("List.foldl")).is_some(),
        "over-applied List.rec (function-building motive) must be recognized"
    );

    // Acc.recOn body eliminates via Acc.rec: well-founded, not structural.
    assert!(
        lower::rec_apply_parts(&env, &peeled("Acc.recOn")).is_none(),
        "Acc.rec (reflexive — well-founded recursion) must refuse"
    );
    // Eq.recOn body eliminates via the INDEXED Eq.rec.
    assert!(
        lower::rec_apply_parts(&env, &peeled("Eq.recOn")).is_none(),
        "Eq.rec (indexed family) must refuse"
    );

    // A partial application (strip one arg off List.length's spine — the
    // major): only the MajorAfterMinors no-major spelling is recognized;
    // stripping ANOTHER arg (a minor) must refuse.
    let spine = peeled("List.length");
    let ExprKind::App(no_major, _) = spine.kind() else {
        panic!("List.length body is an application spine");
    };
    assert!(
        lower::rec_apply_parts(&env, no_major).is_some(),
        "no-major List.rec prefix (the partially applied eliminator) is the \
         rangeAux spelling and must be recognized"
    );
    let ExprKind::App(missing_minor, _) = no_major.kind() else {
        panic!("no-major spine is still an application");
    };
    assert!(
        lower::rec_apply_parts(&env, missing_minor).is_none(),
        "a spine missing a MINOR must refuse (fail-closed partial application)"
    );
}

/// R1 stage-1 upgrades: the eta-shaped `.rec`/`.recOn` wrapper definitions
/// (bare-variable minors, no-major spellings) now lower from source through
/// the synthesized recursive function. Strictly stronger than the previous
/// structured errors / extern drops, and behavior-verified end-to-end by the
/// emit_c differential (`tests/rec_eliminator_e2e.rs`).
#[test]
fn test_r1_eta_rec_wrappers_lower_from_source() {
    let env = full_prelude_env();
    for name in [
        "Nat.recOn",     // eta Nat.rec wrapper (pre-R1: structured error)
        "List.recOn",    // eta List.rec wrapper
        "List.length",   // saturated List.rec, inline minors
        "List.foldl",    // over-applied List.rec (function-building motive)
        "List.rangeAux", // no-major Nat.rec spelling (the def IS the PAP)
    ] {
        assert!(
            matches!(lower_named(&env, name), Ok(Some(_))),
            "{name} must lower from source via the R1 synthesized recursion"
        );
    }
}

/// R1 structural termination: the synthesized `go` for `List.length`
/// self-calls ONLY on the projected tail (`Proj {{ idx: 1 }}` of the
/// scrutinee) — the IH substitution — and the nil arm has no self-call.
#[test]
fn test_r1_synthesized_recursion_is_structural() {
    let env = full_prelude_env();
    let decl = lower_named(&env, "List.length").unwrap().unwrap();
    let crate::lcnf::DeclValue::Code(body) = &decl.body else {
        panic!("List.length lowers to code");
    };

    // Find the synthesized local function (the `go`).
    fn find_fun(code: &Code) -> Option<&FunDecl> {
        match code {
            Code::Fun(decl, rest) => Some(decl).or_else(|| find_fun(rest)),
            Code::Let(_, rest) | Code::JoinPoint(_, rest) => find_fun(rest),
            _ => None,
        }
    }
    let go = find_fun(body).expect("List.length body declares the synthesized go");
    let scrut = go
        .params
        .last()
        .expect("go takes the scrutinee last")
        .fvar_id;
    let Code::Cases(cases) = go.body.as_ref() else {
        panic!("go's body is a Cases over List");
    };
    assert_eq!(cases.type_name.to_string(), "List");
    assert_eq!(cases.scrutinee, scrut);
    assert_eq!(cases.alts.len(), 2, "nil and cons arms");

    // Walk an arm body, collecting (self-call args, tail-proj fvars).
    fn arm_lets(code: &Code) -> Vec<&LetDecl> {
        let mut lets = Vec::new();
        let mut cur = code;
        while let Code::Let(decl, rest) = cur {
            lets.push(decl);
            cur = rest;
        }
        lets
    }
    let mut saw_structural_self_call = false;
    for alt in &cases.alts {
        let (is_cons, body) = match alt {
            Alt::Ctor {
                ctor_name, body, ..
            } => (ctor_name.to_string() == "List.cons", body.as_ref()),
            Alt::Default(body) => (false, body.as_ref()),
        };
        let lets = arm_lets(body);
        let tail_proj: Option<FVarId> = lets
            .iter()
            .find(|l| {
                matches!(
                    &l.value,
                    LetValue::Proj { idx: 1, structure, .. } if *structure == scrut
                )
            })
            .map(|l| l.fvar_id);
        for l in &lets {
            if let LetValue::FVar { fvar, args } = &l.value {
                if *fvar == go.fvar_id {
                    assert!(is_cons, "self-call only in the cons arm");
                    let last = args.last().expect("self-call passes the component");
                    assert_eq!(
                        *last,
                        Arg::FVar(tail_proj.expect("cons arm projects the tail")),
                        "the self-call recurses EXACTLY on the projected tail \
                         (structural termination)"
                    );
                    saw_structural_self_call = true;
                }
            }
        }
    }
    assert!(
        saw_structural_self_call,
        "the cons arm computes its IH by a structural self-call"
    );
}

// ---------------------------------------------------------------------------
// Beta-redex heads (the match-elaboration default-arm shape)
// ---------------------------------------------------------------------------

/// A lambda-headed application LOWERS instead of refusing.
///
/// Match elaboration leaves an unreduced beta-redex in DEFAULT arms — a
/// wildcard arm arrives as `(fun _ : Nat => 0) k` — and the value-position
/// `App` funnel refused it ("Application head: Lam"). Measured blast radius:
/// every fixed multi-arm match (`| 0 => _ | 1 => _ | _ => _`) was blocked from
/// the C extraction lane; the streams flagship's `stepCase` was the finder.
#[test]
fn test_beta_redex_head_lowers() {
    let mut env = full_prelude_env();
    let nat = Expr::const_str("Nat");
    // def redex (k : Nat) : Nat := (fun _ : Nat => 0) k
    let value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::app(
            Expr::lam(BinderInfo::Default, nat.clone(), Expr::nat_lit(0)),
            Expr::bvar(0),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("redex"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        value,
        is_reducible: false,
    })
    .expect("redex must kernel-check");
    assert!(
        matches!(lower_named(&env, "redex"), Ok(Some(_))),
        "a beta-redex head must lower, not refuse with `Application head: Lam`"
    );
}

/// BIND-ONCE: a compound argument to a redex is let-bound once, however many
/// times the binder occurs in the body.
///
/// `(fun x => Nat.add x x) (Nat.succ k)` must compute `Nat.succ k` ONCE.
/// Substituting the raw argument would duplicate its work (and, in the
/// extraction lanes, its overflow `.expect`); only the let-bound ATOM may be
/// substituted. Pinned by counting `Nat.succ` in the lowered code: exactly one
/// occurrence.
#[test]
fn test_beta_redex_compound_argument_is_bound_once() {
    let mut env = full_prelude_env();
    let nat = Expr::const_str("Nat");
    let body = Expr::apps(Expr::const_str("Nat.add"), [Expr::bvar(0), Expr::bvar(0)]);
    let value = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::app(
            Expr::lam(BinderInfo::Default, nat.clone(), body),
            Expr::app(Expr::const_str("Nat.succ"), Expr::bvar(0)),
        ),
    );
    env.add_decl(Declaration::Definition {
        name: Name::from_string("redex2"),
        level_params: vec![],
        type_: Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
        value,
        is_reducible: false,
    })
    .expect("redex2 must kernel-check");
    let decl = lower_named(&env, "redex2")
        .expect("must lower")
        .expect("must produce a decl");
    // The Debug format spells a name as `suffix: ["Nat", "succ"]`, so count
    // that spelling, not the dotted one (which never appears and would make
    // this assertion vacuous in the passing direction and wrong in this one).
    let dumped = format!("{decl:?}");
    assert_eq!(
        dumped.matches(r#"["Nat", "succ"]"#).count(),
        1,
        "the compound argument must be computed ONCE and its atom reused; more \
         than one `Nat.succ` means the argument's work was duplicated:\n{dumped}"
    );
    assert!(
        dumped.matches(r#"["Nat", "add"]"#).count() >= 1,
        "the body must survive the reduction:\n{dumped}"
    );
}

// -- `let` in VALUE position (the `for` / `let mut` lowering gap) -------------

/// A `let` reached in VALUE position — here the RHS of another `let` — must
/// FLATTEN into the enclosing A-normal statement stream, not fail the whole
/// declaration.
///
/// This is the form that stopped `for x in xs do` with a `let mut`
/// accumulator: the reassignment inside the `ForIn` step function is a `let`,
/// and `Id.run`'s inlining leaves the whole `do` block in an argument
/// position, so lowering reached it through `expr_to_let_value` rather than
/// through `expr_to_code`. Only the latter had a `Let` arm, so the declaration
/// died with `Unsupported("Expression form: Let(..)")`.
///
/// Asserting SCOPE, not just success, is the point. A flattening that emits
/// the bindings in the wrong order, or lets the outer binding name the wrong
/// `FVarId`, still "lowers" — and then computes the wrong value at runtime.
#[test]
fn test_let_in_value_position_flattens_in_scope_order() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);

    // let outer : Nat := (let inner : Nat := 7; inner); outer
    let inner = Expr::let_named(
        Name::from_string("inner"),
        Expr::const_str("Nat"),
        Expr::nat_lit(7),
        Expr::bvar(0),
        false,
    );
    let outer = Expr::let_named(
        Name::from_string("outer"),
        Expr::const_str("Nat"),
        inner,
        Expr::bvar(0),
        false,
    );

    let code = expr_to_code(&mut ctx, &outer).expect("a `let` in value position must lower");

    // Collect the flattened bindings in emission order.
    let mut lets = Vec::new();
    let mut cur = &code;
    while let Code::Let(decl, rest) = cur {
        lets.push(decl);
        cur = rest.as_ref();
    }

    assert_eq!(
        lets.len(),
        2,
        "both bindings must survive into one flat stream, got: {lets:?}"
    );

    // The INNER binding is emitted first — it is what the outer one names.
    match &lets[0].value {
        LetValue::Lit(clean_kernel::Literal::Nat(n)) if n.to_u64() == Some(7) => {}
        other => {
            panic!("the inner `let` must be emitted FIRST and bind the literal 7, got {other:?}")
        }
    }

    // The OUTER binding names the inner one, and the terminal returns the outer.
    match &lets[1].value {
        LetValue::FVar { fvar, args } => {
            assert_eq!(
                *fvar, lets[0].fvar_id,
                "the outer binding must name the inner binding's fvar — a \
                 different id here is a mis-scoped flattening, which computes \
                 a wrong value at runtime rather than failing"
            );
            assert!(args.is_empty(), "no application is involved, got {args:?}");
        }
        other => panic!("expected the outer `let` to name the inner fvar, got {other:?}"),
    }

    match cur {
        Code::Return(fv) => assert_eq!(
            *fv, lets[1].fvar_id,
            "the declaration must return the OUTER binding"
        ),
        other => panic!("expected a Return terminal, got {other:?}"),
    }
}

#[test]
fn test_local_value_alias_keeps_parameter_type_and_outer_scope() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let outer = ctx.push_typed_binder(&Expr::const_str("String"));
    let nested = Expr::let_named(
        Name::from_string("inner"),
        Expr::const_str("Nat"),
        Expr::nat_lit(7),
        Expr::bvar(1),
        false,
    );
    let (value, ty) = expr_to_let_value(&mut ctx, &nested).unwrap();
    assert_eq!(ty, Expr::const_str("String"));
    assert!(matches!(value, LetValue::FVar { fvar, args } if fvar == outer && args.is_empty()));
    assert_eq!(ctx.lookup_bvar(0), Some(outer));
    let (value, ty) = expr_to_let_value(&mut ctx, &Expr::fvar(outer)).unwrap();
    assert_eq!(ty, Expr::const_str("String"));
    assert!(matches!(value, LetValue::FVar { fvar, args } if fvar == outer && args.is_empty()));
}

#[test]
fn test_local_value_alias_resolves_dependent_type_before_shadowing() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let outer = ctx.push_typed_binder(&Expr::type_());
    let inner = ctx.push_typed_binder(&Expr::type_());
    let dependent = Expr::app(
        Expr::app(Expr::const_str("Pair"), Expr::bvar(1)),
        Expr::bvar(0),
    );
    let expected = Expr::app(
        Expr::app(Expr::const_str("Pair"), Expr::fvar(outer)),
        Expr::fvar(inner),
    );
    let value = ctx.push_typed_binder(&dependent);
    let (_, ty) = expr_to_let_value(&mut ctx, &Expr::bvar(0)).unwrap();
    assert_eq!(
        ty, expected,
        "type indices belong to the parameter's outer scope"
    );
    let alias = ctx.add_let(
        Name::anon(),
        ty,
        LetValue::FVar {
            fvar: value,
            args: vec![],
        },
    );
    ctx.pop_binder();
    ctx.push_typed_binder(&Expr::const_str("Nat"));
    let (_, ty) = expr_to_let_value(&mut ctx, &Expr::fvar(alias)).unwrap();
    assert_eq!(
        ty, expected,
        "later binders cannot capture the alias's type"
    );
}

#[test]
fn test_lambda_value_alias_records_the_real_parameter_type() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let nat = Expr::const_str("Nat");
    let body = Expr::let_named(
        Name::anon(),
        nat.clone(),
        Expr::bvar(0),
        Expr::bvar(0),
        false,
    );
    let lambda = Expr::lam(BinderInfo::Default, nat.clone(), body);
    let arg = expr_to_arg(&mut ctx, &lambda).unwrap();
    let Arg::FVar(function) = arg else {
        panic!("expected local lambda")
    };
    let code = ctx.wrap_lets(Code::Return(function));
    let Code::Fun(fun, _) = code else {
        panic!("missing lambda declaration")
    };
    let Code::Let(alias, terminal) = fun.body.as_ref() else {
        panic!("missing parameter alias")
    };
    assert_eq!(alias.ty, nat);
    assert!(
        matches!(&alias.value, LetValue::FVar { fvar, args } if *fvar == fun.params[0].fvar_id && args.is_empty())
    );
    assert!(matches!(terminal.as_ref(), Code::Return(id) if *id == alias.fvar_id));
    assert_eq!(ctx.lookup_bvar(0), None);
}

#[test]
fn test_local_value_alias_refuses_missing_bindings_and_types() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    for expr in [Expr::bvar(0), Expr::fvar(FVarId::new(99))] {
        assert!(matches!(
            expr_to_let_value(&mut ctx, &expr),
            Err(CompilerError::InvalidExpr(_))
        ));
    }
    ctx.push_binder(); // A scope-only test binder has no declared type.
    assert!(matches!(
        expr_to_let_value(&mut ctx, &Expr::bvar(0)),
        Err(CompilerError::InvalidExpr(_))
    ));
}

#[test]
fn test_failed_let_body_restores_outer_binder_in_both_positions() {
    let env = make_env();
    for value_position in [false, true] {
        let mut ctx = LcnfContext::new(&env);
        let outer = ctx.push_typed_binder(&Expr::const_str("String"));
        let bad = Expr::let_named(
            Name::anon(),
            Expr::const_str("Nat"),
            Expr::nat_lit(7),
            Expr::bvar(99),
            false,
        );
        if value_position {
            assert!(expr_to_let_value(&mut ctx, &bad).is_err());
        } else {
            assert!(expr_to_code(&mut ctx, &bad).is_err());
        }
        assert_eq!(ctx.lookup_bvar(0), Some(outer));
        assert_eq!(ctx.lookup_bvar(1), None);
    }
}

/// The sibling shape for a bare FREE variable: the beta-redex funnel in
/// `expr_to_let_value` let-binds each argument (BIND-ONCE) and substitutes its
/// ATOM `FVar(f)` for the binder, so `(fun x : Nat => x) 7` reduces to the bare
/// `FVar(f)` and re-enters the funnel as exactly that expression — a form it
/// had no arm for. In value position (here the RHS of a `let`) the reduct must
/// lower to the bound atom itself, and the scope assertions are the same as in
/// the `BVar` pin above: the argument's binding is emitted first, the `let`
/// names it, the terminal returns the `let`.
#[test]
fn test_let_in_value_position_beta_identity_yields_bare_fvar() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let nat = Expr::const_str("Nat");

    // let r : Nat := (fun x : Nat => x) 7; r
    let redex = Expr::app(
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
        Expr::nat_lit(7),
    );
    let decl = Expr::let_named(Name::from_string("r"), nat, redex, Expr::bvar(0), false);

    let code = expr_to_code(&mut ctx, &decl)
        .expect("a beta-redex reducing to its own bound argument must lower");

    let mut lets = Vec::new();
    let mut cur = &code;
    while let Code::Let(decl, rest) = cur {
        lets.push(decl);
        cur = rest.as_ref();
    }

    assert_eq!(
        lets.len(),
        2,
        "the argument's binding and the `let` must both survive, got: {lets:?}"
    );
    match &lets[0].value {
        LetValue::Lit(clean_kernel::Literal::Nat(n)) if n.to_u64() == Some(7) => {}
        other => {
            panic!("the redex argument must be let-bound FIRST to the literal 7, got {other:?}")
        }
    }
    match &lets[1].value {
        LetValue::FVar { fvar, args } => {
            assert_eq!(
                *fvar, lets[0].fvar_id,
                "the `let` must name the argument's atom — the identity redex \
                 reduces to exactly that free variable"
            );
            assert!(args.is_empty(), "no application is involved, got {args:?}");
        }
        other => panic!("expected the `let` to name the argument's fvar, got {other:?}"),
    }
    match cur {
        Code::Return(fv) => assert_eq!(
            *fv, lets[1].fvar_id,
            "the declaration must return the `let`"
        ),
        other => panic!("expected a Return terminal, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// GAP G15: a `theorem` is a PROOF, not code — it must never become a function
// ---------------------------------------------------------------------------

/// GAP G15 — PROOF-TO-EXEC LAUNDERING, closed.
///
/// A `theorem` carries a proof term in `ConstantInfo.value`, so before the
/// `ConstantKind::Theorem` gate it sailed past the two early `Ok(None)` drops
/// (`is_noncomputable`, "no value") and landed in the Prop-valued arm of
/// `constant_to_decl`, which emits the erased-return stub
/// `let r := ⟨erased⟩; return r`. That stub is a REAL `Decl`, and the trust-ir
/// backend turns a real `Decl` into a real `trust_ir::Function` whose erased
/// return is materialized as a boxed zero / NullPtr — i.e. the shared
/// two-language module gained a CALLABLE item with no computational meaning,
/// which the format presents as executable and any module-level quantified
/// statement then silently ranges over.
///
/// A theorem is now dropped exactly as an axiom is: `Ok(None)`, the extern
/// boundary. The decision reads the kernel's own `ConstantKind` (Lean 4 keeps
/// `TheoremVal` distinct from `DefinitionVal` for precisely this reason), not
/// the shape of the type.
#[test]
fn test_theorem_never_lowers_to_a_decl() {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("GapG15.trivialTheorem");
    // `theorem GapG15.trivialTheorem : True := True.intro` — kernel-checked by
    // `add_decl`, so the `ConstantKind::Theorem` under test is stamped by the
    // KERNEL, not hand-written into a `ConstantInfo`.
    env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::const_str("True"),
        value: Expr::const_str("True.intro"),
    })
    .expect("`True.intro : True` kernel-checks against the prelude");

    let info = env.get_const(&name).expect("the theorem is registered");
    // Guard against this test going vacuous if `add_decl` ever stops stamping
    // the kind: the whole point is that the kind is what is consulted.
    assert_eq!(
        info.kind,
        clean_kernel::env::ConstantKind::Theorem,
        "add_decl must stamp Declaration::Theorem as ConstantKind::Theorem"
    );
    // And the precondition of the defect: a theorem DOES carry a value, which
    // is exactly why the two pre-existing `Ok(None)` drops never caught it.
    assert!(
        info.value.is_some(),
        "a theorem carries its proof term as a value — that is the trap"
    );

    let lowered = constant_to_decl(&env, info);
    assert!(
        matches!(lowered, Ok(None)),
        "a theorem must be DROPPED to the extern boundary, never lowered to a \
         Decl (proof-to-exec laundering); got {lowered:?}"
    );
}

/// NOT OVER-FIXED (the companion of `test_theorem_never_lowers_to_a_decl`).
///
/// The erased-stub path exists to keep runtime-irrelevant *definitions*
/// LINKABLE — type-level machinery and Prop-valued class heads are
/// `ConstantKind::Definition`s that other code legitimately references by
/// symbol. The G15 refusal keys on the KIND, not on Prop-ness, so a definition
/// with the very same Prop type and the very same proof-shaped body still
/// lowers to the erased stub.
///
/// If this test ever fails alongside the one above passing, the theorem gate
/// has been widened into the erasure and the two distinct defects have been
/// conflated.
#[test]
fn test_prop_typed_definition_still_emits_the_erased_stub() {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("GapG15.trivialDefinition");
    // Byte-for-byte the same type and value as the theorem above — only the
    // declaration KIND differs.
    env.add_decl(Declaration::Definition {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::const_str("True"),
        value: Expr::const_str("True.intro"),
        is_reducible: false,
    })
    .expect("`True.intro : True` kernel-checks as a definition too");

    let info = env.get_const(&name).expect("the definition is registered");
    assert_eq!(
        info.kind,
        clean_kernel::env::ConstantKind::Definition,
        "the companion must actually be a Definition, or it proves nothing"
    );

    let decl = constant_to_decl(&env, info)
        .expect("a Prop-valued definition lowers")
        .expect("a Prop-valued definition must keep emitting its erased stub");
    let crate::lcnf::DeclValue::Code(code) = &decl.body else {
        panic!("expected a Code body");
    };
    let Code::Let(let_decl, rest) = code.as_ref() else {
        panic!("expected `let _ := ⟨erased⟩; ..`, got {code:?}");
    };
    assert!(
        matches!(let_decl.value, LetValue::Erased),
        "the stub must bind the erased token, got {:?}",
        let_decl.value
    );
    assert!(
        matches!(rest.as_ref(), Code::Return(fv) if *fv == let_decl.fvar_id),
        "the stub must return its erased binding"
    );
}

/// GAP G15 AT SCALE — the module-wide gate.
///
/// The single hand-built theorem above pins the mechanism; this pins the
/// POPULATION. `constant_to_decl` must drop EVERY `ConstantKind::Theorem` in
/// the environment, so no theorem anywhere in a module can reach the backend
/// as a `Decl` (and therefore as a callable `trust_ir::Function`).
///
/// Measured with the gate disabled on 2026-09-01: the full prelude carries
/// 332 theorems and ALL 332 lowered to `Ok(Some(Decl))` with the erased-return
/// stub body — a 100% laundering rate, not an edge case. With the gate: 0.
///
/// The floor assertion keeps the test from going vacuous if the prelude ever
/// stops registering theorems.
#[test]
fn test_no_prelude_theorem_ever_lowers_to_a_decl() {
    let env = full_prelude_env();
    let theorems: Vec<clean_kernel::ConstantInfo> = env
        .constants()
        .filter(|c| c.kind == clean_kernel::env::ConstantKind::Theorem)
        .cloned()
        .collect();
    assert!(
        theorems.len() > 250,
        "prelude theorem population collapsed ({}) — this gate would be vacuous",
        theorems.len()
    );

    let leaked: Vec<String> = theorems
        .iter()
        .filter(|info| matches!(constant_to_decl(&env, info), Ok(Some(_))))
        .map(|info| info.name.to_string())
        .collect();
    assert!(
        leaked.is_empty(),
        "{} of {} prelude theorems were lowered to emitted Decls \
         (proof-to-exec laundering); first offenders: {:?}",
        leaked.len(),
        theorems.len(),
        &leaked[..leaked.len().min(10)]
    );
}

// ---------------------------------------------------------------------------
// The ADJACENT question the theorem gate deliberately left open: `opaque`
// ---------------------------------------------------------------------------

/// An `opaque` constant IS code — the doc that said otherwise was wrong.
///
/// A `ConstantKind::Opaque` clears the same "no value" drop a theorem used to
/// clear, because `Declaration::Opaque.value` is not an `Option`: every opaque
/// the kernel stamps arrives with `value: Some(..)`. So the shape of the trap
/// is IDENTICAL to G15 — and the answer is the OPPOSITE one. An `opaque` body
/// is real runtime content that is merely δ-irreducible for the type checker;
/// dropping it would turn every caller's reference into a dangling extern (a
/// link error), not into a safe refusal. It therefore lowers exactly like a
/// definition, and `constant_to_decl`'s doc now says so.
///
/// This test is the pin: if someone ever "completes" the G15 fix by adding
/// `| ConstantKind::Opaque` to the theorem gate, it fails here rather than at
/// link time in a downstream repo.
#[test]
fn test_value_bearing_opaque_still_lowers_to_a_decl() {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("GapG15.opaqueValue");
    // `opaque GapG15.opaqueValue : Nat := Nat.zero` — kernel-checked, so the
    // `ConstantKind::Opaque` under test is stamped by the KERNEL.
    env.add_decl(Declaration::Opaque {
        name: name.clone(),
        level_params: vec![],
        type_: Expr::const_str("Nat"),
        value: Expr::const_str("Nat.zero"),
    })
    .expect("`Nat.zero : Nat` kernel-checks against the prelude");

    let info = env.get_const(&name).expect("the opaque is registered");
    assert_eq!(
        info.kind,
        clean_kernel::env::ConstantKind::Opaque,
        "add_decl must stamp Declaration::Opaque as ConstantKind::Opaque"
    );
    // The precondition that makes this the same trap as the theorem: an opaque
    // DOES carry a value, so the "no value" drop never sees it.
    assert!(
        info.value.is_some(),
        "a kernel-stamped opaque always carries its body — that is why the \
         `None => Ok(None)` arm cannot be what handles opaques"
    );

    let decl = constant_to_decl(&env, info)
        .expect("an opaque with a computable body lowers")
        .expect(
            "a value-bearing opaque must NOT be dropped — a dropped opaque \
                 that something calls is a link error, not a refusal",
        );
    let crate::lcnf::DeclValue::Code(code) = &decl.body else {
        panic!("expected a Code body");
    };
    // And it must carry REAL CONTENT, not the erased stub: `Nat` is neither
    // Prop-valued nor type-level machinery, so nothing here may erase it.
    if let Code::Let(let_decl, _) = code.as_ref() {
        assert!(
            !matches!(let_decl.value, LetValue::Erased),
            "a data-returning opaque must not be erased to the ⟨erased⟩ stub"
        );
    }
}

/// The one `Opaque` that IS dropped — and the reason it is not a
/// counter-example to the test above.
///
/// `clean_olean`'s trusted-import path registers a value-LESS
/// `ConstantKind::Opaque` TYPE STUB for a proof body the types-only loader
/// skipped (`convert_parsed_constant_to_type_stub`; the kind is deliberately
/// kept as `Opaque` rather than `Axiom` so the axiom set is not inflated).
/// That stub has nothing to lower, so it takes the "no value" drop and behaves
/// as an axiom does. The DROP IS DRIVEN BY THE ABSENT VALUE, never by the kind
/// — which is exactly what makes the doc's old "None for axioms/opaque" claim
/// wrong rather than merely imprecise.
#[test]
fn test_value_less_opaque_type_stub_is_dropped() {
    let mut env = Environment::with_prelude();
    let name = Name::from_string("GapG15.opaqueTypeStub");
    // Built the way the trusted importer builds it: a `ConstantInfo` with the
    // `Opaque` kind and NO value. `add_decl` cannot express this (the
    // `Declaration::Opaque` value field is not optional), so this goes through
    // the same `extend_constants_unchecked` hook the importer uses.
    env.extend_constants_unchecked(std::iter::once(
        clean_kernel::env::ConstantInfo::new_with_reducibility(
            name.clone(),
            vec![],
            Expr::const_str("Nat"),
            None,
            clean_kernel::env::Reducibility::Opaque,
            clean_kernel::env::ConstantKind::Opaque,
        ),
    ));

    let info = env.get_const(&name).expect("the stub is registered");
    assert_eq!(
        info.kind,
        clean_kernel::env::ConstantKind::Opaque,
        "the stub must really be an Opaque, or it proves nothing"
    );
    assert!(info.value.is_none(), "a type stub carries no body");

    let lowered = constant_to_decl(&env, info);
    assert!(
        matches!(lowered, Ok(None)),
        "a value-less opaque has nothing to lower and takes the extern \
         boundary; got {lowered:?}"
    );
}

#[test]
fn test_value_variable_atoms_preserve_identity_and_refuse_unbound_indices() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let outer = ctx.push_typed_binder(&Expr::const_str("Nat"));
    let inner = ctx.push_typed_binder(&Expr::const_str("Nat"));
    for (expr, expected) in [
        (Expr::bvar(0), inner),
        (Expr::bvar(1), outer),
        (Expr::fvar(outer), outer),
    ] {
        let (value, ty) = expr_to_let_value(&mut ctx, &expr).expect("variable atom must lower");
        assert!(
            matches!(value, LetValue::FVar { fvar, args } if fvar == expected && args.is_empty())
        );
        // The merged lowerer carries declared local types through atom aliases.
        assert_eq!(ty, Expr::const_str("Nat"));
    }
    for idx in [2, Expr::MAX_BVAR_INDEX] {
        assert!(matches!(
            expr_to_let_value(&mut ctx, &Expr::bvar(idx)),
            Err(CompilerError::InvalidExpr(_))
        ));
    }
    assert_eq!(ctx.bvar_stack, vec![outer, inner]);
    assert!(ctx.take_lets().is_empty());
}

/// This ordinary-runtime fixture cannot reach the lowerer: kernel metadata
/// rejects the original over-limit input when constructing the expression.
#[test]
#[should_panic(expected = "too many bound variables")]
fn test_value_variable_fixture_rejects_unrepresentable_kernel_index() {
    let _ = Expr::bvar(u32::MAX);
}

#[test]
fn test_value_let_resolves_outer_index_and_restores_scope() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let outer = ctx.push_typed_binder(&Expr::const_str("Nat"));
    let value = Expr::let_named(
        Name::from_string("inner"),
        Expr::const_str("Nat"),
        Expr::nat_lit(7),
        Expr::bvar(1),
        false,
    );
    let (value, _) = expr_to_let_value(&mut ctx, &value).expect("outer variable remains in scope");
    assert!(matches!(value, LetValue::FVar { fvar, args } if fvar == outer && args.is_empty()));
    assert_eq!(ctx.bvar_stack, vec![outer]);
    let lets = ctx.take_lets();
    assert_eq!(lets.len(), 1);
    assert_ne!(lets[0].fvar_id, outer);
    assert!(
        matches!(&lets[0].value, LetValue::Lit(clean_kernel::Literal::Nat(n)) if n.to_u64() == Some(7))
    );
}

#[test]
fn test_value_and_code_let_restore_scope_on_body_refusal() {
    let env = make_env();
    for code_position in [false, true] {
        let mut ctx = LcnfContext::new(&env);
        let outer = ctx.push_typed_binder(&Expr::const_str("Nat"));
        let value = Expr::let_named(
            Name::from_string("inner"),
            Expr::const_str("Nat"),
            Expr::nat_lit(7),
            Expr::bvar(2),
            false,
        );
        let result = if code_position {
            expr_to_code(&mut ctx, &value).map(|_| ())
        } else {
            expr_to_let_value(&mut ctx, &value).map(|_| ())
        };
        assert!(matches!(result, Err(CompilerError::InvalidExpr(_))));
        assert_eq!(ctx.bvar_stack, vec![outer]);
        assert_eq!(ctx.lookup_bvar(0), Some(outer));
        assert_eq!(ctx.lookup_bvar(1), None);
    }
}

#[test]
fn test_beta_identity_value_reuses_its_single_argument_binding() {
    let env = make_env();
    let mut ctx = LcnfContext::new(&env);
    let value = Expr::app(
        Expr::lam(BinderInfo::Default, Expr::const_str("Nat"), Expr::bvar(0)),
        Expr::nat_lit(7),
    );
    let (value, _) = expr_to_let_value(&mut ctx, &value).expect("identity beta body is an atom");
    let lets = ctx.take_lets();
    assert_eq!(lets.len(), 1, "the argument must be bound exactly once");
    assert!(
        matches!(&lets[0].value, LetValue::Lit(clean_kernel::Literal::Nat(n)) if n.to_u64() == Some(7))
    );
    assert!(
        matches!(value, LetValue::FVar { fvar, args } if fvar == lets[0].fvar_id && args.is_empty())
    );
    assert!(ctx.bvar_stack.is_empty());
}
