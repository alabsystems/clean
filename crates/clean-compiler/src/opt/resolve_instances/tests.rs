// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS6.4 unit tests: the rule reads instance VALUES (never names), unfolds
//! only instances, within the budget, and the `UIntW.ofNat` fold is exact at
//! its boundaries.

use super::*;
use crate::lcnf::Param;
use clean_kernel::env::{ConstantInfo, Declaration};
use clean_kernel::{KernelInstanceInfo, DEFAULT_INSTANCE_PRIORITY};

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn prelude() -> Environment {
    Environment::try_with_prelude().expect("prelude environment")
}

fn u64t() -> Expr {
    Expr::const_str("UInt64")
}

/// `HAdd UInt64 UInt64 UInt64`.
fn hadd_u64_ty() -> Expr {
    Expr::apps(
        Expr::const_(n("HAdd"), vec![Level::zero(), Level::zero(), Level::zero()]),
        [u64t(), u64t(), u64t()],
    )
}

/// `HAdd.mk UInt64 UInt64 UInt64 <op>`.
fn hadd_mk_u64(op: &str) -> Expr {
    Expr::apps(
        Expr::const_(
            n("HAdd.mk"),
            vec![Level::zero(), Level::zero(), Level::zero()],
        ),
        [u64t(), u64t(), u64t(), Expr::const_str(op)],
    )
}

/// Add a kernel-checked `HAdd UInt64 UInt64 UInt64` definition.
fn add_hadd_def(env: &mut Environment, name: &str, value: Expr) {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_: hadd_u64_ty(),
        value,
        is_reducible: true,
    })
    .unwrap_or_else(|e| panic!("`{name}` kernel-checks: {e:?}"));
}

fn register_hadd_instance(env: &mut Environment, name: &str) {
    env.register_instance(KernelInstanceInfo {
        name: n(name),
        class_name: n("HAdd"),
        priority: DEFAULT_INSTANCE_PRIORITY,
        type_: None,
        value: None,
    });
}

fn let_(id: u64, ty: Expr, value: LetValue, body: Code) -> Code {
    Code::Let(
        LetDecl::new(FVarId::new(id), n(&format!("_{id}")), ty, value),
        Box::new(body),
    )
}

fn fv(id: u64) -> Arg {
    Arg::FVar(FVarId::new(id))
}

/// `fun (x y : UInt64) => let inst := <inst>; let r := HAdd.hAdd _ _ _ inst
/// x y[..method_args]; return r` — the post-`to_mono` spelling of `x + y`.
fn method_call_decl(inst: &str, method_args: usize) -> Decl {
    let mut args = vec![Arg::Erased, Arg::Erased, Arg::Erased, fv(3)];
    args.extend([fv(1), fv(2)].into_iter().take(method_args));
    Decl {
        name: n("ws6_4_probe"),
        level_params: vec![],
        ty: Expr::arrow(u64t(), Expr::arrow(u64t(), u64t())),
        params: vec![
            Param::new(FVarId::new(1), n("x"), u64t()),
            Param::new(FVarId::new(2), n("y"), u64t()),
        ],
        body: DeclValue::Code(Box::new(let_(
            3,
            Expr::const_str("lcAny"),
            LetValue::Const {
                name: n(inst),
                levels: vec![],
                args: vec![],
            },
            let_(
                4,
                u64t(),
                LetValue::Const {
                    name: n("HAdd.hAdd"),
                    levels: vec![],
                    args,
                },
                Code::Return(FVarId::new(4)),
            ),
        ))),
        recursive: false,
    }
}

/// The value bound to fvar 4 (the method call's result) after the pass, and
/// whether the instance binding (fvar 3) survived.
fn result_value(decl: &Decl) -> (LetValue, bool) {
    fn walk(code: &Code, found: &mut Option<LetValue>, inst_live: &mut bool) {
        if let Code::Let(d, body) = code {
            if d.fvar_id == FVarId::new(4) {
                *found = Some(d.value.clone());
            }
            if d.fvar_id == FVarId::new(3) {
                *inst_live = true;
            }
            walk(body, found, inst_live);
        }
    }
    let DeclValue::Code(code) = &decl.body else {
        panic!("code body");
    };
    let mut found = None;
    let mut inst_live = false;
    walk(code, &mut found, &mut inst_live);
    (found.expect("the call binding survives"), inst_live)
}

fn native(name: &str) -> LetValue {
    LetValue::Const {
        name: n(name),
        levels: vec![],
        args: vec![fv(1), fv(2)],
    }
}

/// Assert the call is left EXACTLY as it was.
fn assert_unchanged(env: &Environment, decl: &Decl) {
    let out = resolve_known_instances(decl, env);
    assert_eq!(&out, decl, "a call outside the rule must be left unchanged");
}

#[test]
fn test_class_projection_reads_the_projection_value() {
    let env = prelude();
    assert_eq!(
        class_projection(&env, &n("HAdd.hAdd")),
        Some(ClassProjection {
            class: n("HAdd"),
            field: 0,
            inst_pos: 3,
        })
    );
    // Not projection functions: an operation, a definition over a
    // non-class, a missing name.
    assert_eq!(class_projection(&env, &n("UInt64.add")), None);
    assert_eq!(class_projection(&env, &n("Nat.add")), None);
    assert_eq!(class_projection(&env, &n("ws6_4_absent")), None);
}

/// Positive control on the real prelude: `x + y : UInt64` resolves to the
/// native `UInt64.add x y`, and the dead instance binding is swept.
#[test]
fn test_prelude_hadd_uint64_resolves_to_uint64_add() {
    let env = prelude();
    let out = resolve_known_instances(&method_call_decl("instHAddUInt64", 2), &env);
    let (value, inst_live) = result_value(&out);
    assert_eq!(value, native("UInt64.add"));
    assert!(!inst_live, "the orphaned instance binding must be swept");
}

/// A field whose compiled meaning is not its value (`@[implemented_by]` or
/// `@[extern]`) never becomes a direct call: the call is left exactly as it
/// was, so `to_lcnf`'s substitution or the native extern refusal decides what
/// runs. A direct call to the field's own name would run its kernel body.
#[test]
fn test_field_with_compiler_attr_is_not_resolved() {
    let decl = method_call_decl("instHAddUInt64", 2);
    let mut by_impl = prelude();
    by_impl.register_implemented_by(n("UInt64.add"), n("UInt64.sub"));
    assert_unchanged(&by_impl, &decl);
    let mut by_extern = prelude();
    by_extern.register_extern(n("UInt64.add"), "my_u64_add".to_owned());
    assert_unchanged(&by_extern, &decl);
}

/// Every delta step needs runtime custody, including an aliased instance's
/// target. A kernel field must not replace the external/noncomputable value.
#[test]
fn test_instance_delta_chain_with_compiler_attr_is_not_resolved() {
    let with_alias = || {
        let mut env = prelude();
        add_hadd_def(&mut env, "ws6_4_alias", Expr::const_str("instHAddUInt64"));
        register_hadd_instance(&mut env, "ws6_4_alias");
        env
    };
    for target in ["instHAddUInt64", "ws6_4_alias"] {
        let mut by_extern = with_alias();
        by_extern.register_extern(n(target), "external_instance".to_owned());
        assert_unchanged(&by_extern, &method_call_decl("ws6_4_alias", 2));
        let mut noncomputable = with_alias();
        noncomputable.mark_noncomputable(n(target));
        assert_unchanged(&noncomputable, &method_call_decl("ws6_4_alias", 2));
    }
}

/// MUTATION CONTROL: in a hand-built environment where `instHAddUInt64 :=
/// HAdd.mk UInt64.sub`, the rewrite produces `sub`, never `add` — it reads
/// the instance's VALUE, not its name.
#[test]
fn test_rewrite_reads_the_value_not_the_name() {
    let mut env = prelude();
    // Re-bind the prelude instance's value (a type-correct `HAdd.mk`),
    // keeping its instance registration.
    env.add_constant_unchecked_for_test(ConstantInfo::new(
        n("instHAddUInt64"),
        vec![],
        hadd_u64_ty(),
        Some(hadd_mk_u64("UInt64.sub")),
        true,
    ));
    let out = resolve_known_instances(&method_call_decl("instHAddUInt64", 2), &env);
    let (value, _) = result_value(&out);
    assert_eq!(value, native("UInt64.sub"));
    assert_ne!(value, native("UInt64.add"));
}

/// MUTATION CONTROL: a constant with exactly an instance's shape that is NOT
/// a registered instance is never unfolded.
#[test]
fn test_non_instance_constant_is_not_unfolded() {
    let mut env = prelude();
    add_hadd_def(&mut env, "ws6_4_notAnInstance", hadd_mk_u64("UInt64.add"));
    assert!(!env.is_instance(&n("ws6_4_notAnInstance")));
    assert_unchanged(&env, &method_call_decl("ws6_4_notAnInstance", 2));

    // The same value registered as an instance does resolve (the twin).
    register_hadd_instance(&mut env, "ws6_4_notAnInstance");
    let out = resolve_known_instances(&method_call_decl("ws6_4_notAnInstance", 2), &env);
    assert_eq!(result_value(&out).0, native("UInt64.add"));
}

/// An instance alias of a non-instance is not unfolded either: every δ-step
/// must land on an instance.
#[test]
fn test_delta_chain_through_a_non_instance_stops() {
    let mut env = prelude();
    add_hadd_def(&mut env, "ws6_4_plain", hadd_mk_u64("UInt64.add"));
    add_hadd_def(&mut env, "ws6_4_alias", Expr::const_str("ws6_4_plain"));
    register_hadd_instance(&mut env, "ws6_4_alias");
    assert_unchanged(&env, &method_call_decl("ws6_4_alias", 2));
}

/// The δ budget: a chain of exactly [`MAX_INSTANCE_UNFOLD`] instance
/// constants resolves; one more does not.
#[test]
fn test_delta_budget_boundary() {
    let mut env = prelude();
    // chain_k := chain_{k-1}, chain_0 := instHAddUInt64 (all instances).
    let mut prev = "instHAddUInt64".to_string();
    for k in 0..MAX_INSTANCE_UNFOLD {
        let name = format!("ws6_4_chain_{k}");
        add_hadd_def(&mut env, &name, Expr::const_str(&prev));
        register_hadd_instance(&mut env, &name);
        prev = name;
    }
    // `ws6_4_chain_{K-2}` needs K δ-steps (K-1 aliases + the instance).
    let within = format!("ws6_4_chain_{}", MAX_INSTANCE_UNFOLD - 2);
    let out = resolve_known_instances(&method_call_decl(&within, 2), &env);
    assert_eq!(result_value(&out).0, native("UInt64.add"));
    // `ws6_4_chain_{K-1}` needs K+1: left unchanged.
    let beyond = format!("ws6_4_chain_{}", MAX_INSTANCE_UNFOLD - 1);
    assert_unchanged(&env, &method_call_decl(&beyond, 2));
}

/// NEGATIVE TWIN (kernel level): an instance whose value is a computation —
/// here a β-redex `(fun _ => HAdd.mk UInt64.add) 0`, the shape a `match`
/// or any `let` also has — is not a literal `mk` application, so the
/// dynamic call stays.
#[test]
fn test_computed_instance_value_keeps_the_dynamic_call() {
    let mut env = prelude();
    let redex = Expr::app(
        Expr::lam(
            clean_kernel::BinderInfo::Default,
            Expr::const_str("Nat"),
            hadd_mk_u64("UInt64.add"),
        ),
        Expr::nat_lit(0),
    );
    add_hadd_def(&mut env, "ws6_4_computed", redex);
    register_hadd_instance(&mut env, "ws6_4_computed");
    assert_unchanged(&env, &method_call_decl("ws6_4_computed", 2));
}

/// A partial application of the method (one of two arguments) is left
/// unchanged: only saturated calls are rewritten.
#[test]
fn test_partial_application_is_unchanged() {
    let env = prelude();
    assert_unchanged(&env, &method_call_decl("instHAddUInt64", 1));
    assert_unchanged(&env, &method_call_decl("instHAddUInt64", 0));
}

// ---- the companion `UIntW.ofNat (Lit n)` fold --------------------------

#[test]
fn test_fold_uint_of_nat_boundaries() {
    assert_eq!(fold_uint_of_nat(8, &BigNat::from_u64(256)), 0);
    assert_eq!(fold_uint_of_nat(8, &BigNat::from_u64(255)), 255);
    assert_eq!(fold_uint_of_nat(8, &BigNat::from_u64(257)), 1);
    assert_eq!(fold_uint_of_nat(16, &BigNat::from_u64(65_536)), 0);
    assert_eq!(fold_uint_of_nat(16, &BigNat::from_u64(65_535)), 65_535);
    assert_eq!(fold_uint_of_nat(32, &BigNat::from_u64(1 << 32)), 0);
    assert_eq!(
        fold_uint_of_nat(32, &BigNat::from_u64(u64::from(u32::MAX))),
        u64::from(u32::MAX)
    );
    // 2^64 + 3 (two limbs).
    assert_eq!(fold_uint_of_nat(64, &BigNat::from_limbs(vec![3, 1])), 3);
    assert_eq!(fold_uint_of_nat(64, &BigNat::from_u64(u64::MAX)), u64::MAX);
    // 2^128 + 5 (three limbs) at width 8.
    assert_eq!(fold_uint_of_nat(8, &BigNat::from_limbs(vec![5, 0, 1])), 5);
}

/// `let n : Nat := <lit>; let x : UIntW := UIntW.ofNat n; return x`.
fn of_nat_decl(carrier: &str, lit: BigNat, declared: &str) -> Decl {
    Decl {
        name: n("ws6_4_lit"),
        level_params: vec![],
        ty: Expr::const_str(carrier),
        params: vec![],
        body: DeclValue::Code(Box::new(let_(
            1,
            Expr::const_str("Nat"),
            LetValue::Lit(Literal::Nat(lit)),
            let_(
                2,
                Expr::const_str(declared),
                LetValue::Const {
                    name: n(&format!("{carrier}.ofNat")),
                    levels: vec![],
                    args: vec![fv(1)],
                },
                Code::Return(FVarId::new(2)),
            ),
        ))),
        recursive: false,
    }
}

fn folded(decl: &Decl) -> Option<u64> {
    let DeclValue::Code(code) = &decl.body else {
        return None;
    };
    match code.as_ref() {
        Code::Let(d, body)
            if d.fvar_id == FVarId::new(2) && matches!(body.as_ref(), Code::Return(_)) =>
        {
            match &d.value {
                LetValue::Lit(Literal::Nat(v)) => v.to_u64(),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The fold through the pass, at the three spec boundaries, with the dead
/// `Nat` literal swept.
#[test]
fn test_of_nat_fold_through_the_pass() {
    let env = prelude();
    let cases = [
        ("UInt8", BigNat::from_u64(256), 0),
        ("UInt8", BigNat::from_u64(255), 255),
        ("UInt64", BigNat::from_limbs(vec![3, 1]), 3),
    ];
    for (carrier, lit, want) in cases {
        let out = resolve_known_instances(&of_nat_decl(carrier, lit.clone(), carrier), &env);
        assert_eq!(folded(&out), Some(want), "{carrier}.ofNat {lit:?}");
    }
}

/// The fold fires only at a declared type of exactly `UIntW`, and only on a
/// `Nat` literal: anything else is left unchanged.
#[test]
fn test_of_nat_fold_requires_exact_declared_type() {
    let env = prelude();
    assert_unchanged(&env, &of_nat_decl("UInt8", BigNat::from_u64(7), "lcAny"));
    assert_unchanged(&env, &of_nat_decl("UInt8", BigNat::from_u64(7), "UInt16"));
    // An environment without the prelude's `UInt8.ofNat` never folds.
    assert_unchanged(
        &Environment::new(),
        &of_nat_decl("UInt8", BigNat::from_u64(7), "UInt8"),
    );
}

// ---- review: callees `to_mono` would rewrite are never emitted raw ------

/// `Nat.succ` and `Decidable.decide` are closed constants a structure-class
/// field can hold, but `to_mono` rewrites each at a source-level call, so a
/// raw `f x…` after `to_mono` would bypass that; `UInt64.add` is a fixed
/// point and stays resolvable.
#[test]
fn test_resolved_call_must_already_be_mono() {
    let env = prelude();
    let call = |f: &str, args: Vec<Arg>| LetValue::Const {
        name: n(f),
        levels: vec![],
        args,
    };
    assert!(resolved_call_is_mono(
        &env,
        &call("UInt64.add", vec![fv(1), fv(2)])
    ));
    assert!(!resolved_call_is_mono(&env, &call("Nat.succ", vec![fv(1)])));
    assert!(!resolved_call_is_mono(
        &env,
        &call("Decidable.decide", vec![Arg::Erased, fv(1)])
    ));
}

/// Only first-order, runtime-callable constants resolve: a data function
/// does; a type former, a recursor, and a function with a `Prop`/`Sort`
/// binder (`Decidable.decide`'s `p`) do not.
#[test]
fn test_runtime_callable_field() {
    let env = prelude();
    assert!(runtime_callable_field(&env, &n("UInt64.add")));
    assert!(runtime_callable_field(&env, &n("Nat.succ")));
    for no in [
        "Nat",
        "UInt64",
        "Nat.rec",
        "Decidable.decide",
        "ws6_4_absent",
    ] {
        assert!(!runtime_callable_field(&env, &n(no)), "{no}");
    }
}
