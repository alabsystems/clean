// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! The fenced kernel reads an ordinary constant's `MData` as its body,
//! measured judgment by judgment on the pinned toolchain's own extension keys
//! (Q4 residuals, 2026-11-14).
//!
//! The binding fingerprint erases `MData` from ordinary constants
//! (`fingerprint.rs`, `Annotations`).
//! That is sound only while every judgment the replay and the by-name
//! extension rely on gives a wrapped term the answer it gives the unwrapped
//! one. These arms take each key whose own type or value carries `MData` in
//! v4.30.0-rc2's `Init`, re-admit its cone through the fenced reference entry
//! (`reference_base_closed`, under the pinned binding table), and check, on
//! the value and the type as Lean wrote them, with every wrapper erased, with
//! a wrapper around every node, and with a wrapper around each single node:
//!
//! - checking each value form against each type form
//!   (`ReferenceKernel::check_closed_term`);
//! - inference (`infer_type`), the inferred type equal to every type form, and
//!   inference commuting with erasure;
//! - definitional equality of the forms with each other and with the constant;
//! - the by-name extension's answer on literals, which is the native one;
//! - `whnf` of the value applied to literals, equal up to erasure, and, where
//!   the key recurses structurally (`UNFOLDS`), the native value (a wrong
//!   literal is a negative control);
//! - instantiation of the value's and the type's bodies, which commutes with
//!   erasure.
//!
//! The second arm shows the erasure moves exactly the keys whose ordinary
//! cone carries a wrapper, so the re-pin of the worlds moved those rows and
//! no other.

use super::super::super::fingerprint::Fingerprinter;
use super::super::super::ClosedRecheckOptions;
use super::super::{declares, EXTENSION_KEYS};
use super::load_key_modules;
use clean_kernel::env::{ConstantKind, Environment};
use clean_kernel::expr::{Expr, ExprKind, MDataValue};
use clean_kernel::name::Name;
use clean_kernel::TypeChecker;
use std::collections::BTreeSet;
use std::sync::Arc;

/// The keys whose own type or value carries `MData` in v4.30.0-rc2's `Init`
/// (measured by this file's first arm; a toolchain move that changes the set
/// fails it). lean4export strips every wrapper; the `.olean` keeps them.
const CARRIERS: &[&str] = &[
    "Int.add",
    "Int.mul",
    "Int.sub",
    "Nat.add",
    "Nat.beq",
    "Nat.ble",
    "Nat.div",
    "Nat.gcd",
    "Nat.land",
    "Nat.lor",
    "Nat.mod",
    "Nat.mul",
    "Nat.pow",
    "Nat.pred",
    "Nat.shiftLeft",
    "Nat.shiftRight",
    "Nat.sub",
    "Nat.xor",
];

/// The carriers whose value, unfolded on literals, reaches the native answer
/// by structural recursion. The others recurse well-foundedly (their `whnf`
/// on literals reduces through `Acc.rec` proofs), so their unfolding is not
/// compared; every other judgment is.
const UNFOLDS: &[&str] = &[
    "Int.add",
    "Int.mul",
    "Int.sub",
    "Nat.add",
    "Nat.beq",
    "Nat.ble",
    "Nat.mul",
    "Nat.pow",
    "Nat.pred",
    "Nat.shiftLeft",
    "Nat.sub",
];

fn has_mdata(e: &Expr) -> bool {
    let mut stack = vec![e];
    while let Some(x) = stack.pop() {
        if matches!(x.kind(), ExprKind::MData(..)) {
            return true;
        }
        stack.extend(children(x));
    }
    false
}

fn children(e: &Expr) -> Vec<&Expr> {
    match e.kind() {
        ExprKind::App(f, a) => vec![f.as_ref(), a.as_ref()],
        ExprKind::Lam(_, t, b) | ExprKind::Pi(_, t, b) => vec![t.as_ref(), b.as_ref()],
        ExprKind::Let(_, t, v, b, _) => vec![t.as_ref(), v.as_ref(), b.as_ref()],
        ExprKind::Proj(_, _, x) | ExprKind::MData(_, x) => vec![x.as_ref()],
        _ => Vec::new(),
    }
}

/// `e` with each immediate child replaced by `f(child)`.
fn rebuild(e: &Expr, f: &mut dyn FnMut(&Expr) -> Expr) -> Expr {
    let kind = match e.kind() {
        ExprKind::App(a, b) => {
            let a = f(a);
            ExprKind::App(Arc::new(a), Arc::new(f(b)))
        }
        ExprKind::Lam(bd, t, b) => {
            let t = f(t);
            ExprKind::Lam(*bd, Arc::new(t), Arc::new(f(b)))
        }
        ExprKind::Pi(bd, t, b) => {
            let t = f(t);
            ExprKind::Pi(*bd, Arc::new(t), Arc::new(f(b)))
        }
        ExprKind::Let(n, t, v, b, nd) => {
            let t = f(t);
            let v = f(v);
            ExprKind::Let(n.clone(), Arc::new(t), Arc::new(v), Arc::new(f(b)), *nd)
        }
        ExprKind::Proj(s, i, x) => ExprKind::Proj(s.clone(), *i, Arc::new(f(x))),
        ExprKind::MData(m, x) => ExprKind::MData(m.clone(), Arc::new(f(x))),
        _ => return e.clone(),
    };
    Expr::from_kind(kind)
}

/// `e` with every `MData` wrapper removed.
fn erase(e: &Expr) -> Expr {
    match e.kind() {
        ExprKind::MData(_, x) => erase(x),
        _ => rebuild(e, &mut erase),
    }
}

fn mark(e: Expr) -> Expr {
    Expr::mdata(
        vec![(Name::from_string("q4.residuals"), MDataValue::Nat(7))],
        e,
    )
}

/// `e` with a wrapper around every node.
fn wrap_all(e: &Expr) -> Expr {
    mark(rebuild(e, &mut wrap_all))
}

/// `e` with a wrapper around the node at pre-order position `at` only.
fn wrap_at(e: &Expr, at: usize) -> Expr {
    fn go(e: &Expr, at: usize, next: &mut usize) -> Expr {
        let here = *next;
        *next += 1;
        let rebuilt = rebuild(e, &mut |c| go(c, at, next));
        if here == at {
            mark(rebuilt)
        } else {
            rebuilt
        }
    }
    go(e, at, &mut 0)
}

fn node_count(e: &Expr) -> usize {
    1 + children(e).into_iter().map(node_count).sum::<usize>()
}

fn nat_lit(n: u64) -> Expr {
    Expr::nat_lit(n)
}

fn konst(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), Vec::new())
}

fn int_lit(n: i64) -> Expr {
    if n >= 0 {
        Expr::app(konst("Int.ofNat"), nat_lit(n.unsigned_abs()))
    } else {
        Expr::app(konst("Int.negSucc"), nat_lit(n.unsigned_abs() - 1))
    }
}

fn bool_lit(b: bool) -> Expr {
    konst(if b { "Bool.true" } else { "Bool.false" })
}

/// The native answer of `key` at `args`, as a kernel value.
fn native(key: &str, args: &[u64]) -> Expr {
    let i = |k: usize| i64::try_from(args[k]).expect("small literal");
    match (key, args) {
        ("Int.add", [_, _]) => int_lit(i(0) + i(1)),
        ("Int.mul", [_, _]) => int_lit(i(0) * i(1)),
        ("Int.sub", [_, _]) => int_lit(i(0) - i(1)),
        ("Nat.add", [a, b]) => nat_lit(a + b),
        ("Nat.beq", [a, b]) => bool_lit(a == b),
        ("Nat.ble", [a, b]) => bool_lit(a <= b),
        ("Nat.div", [a, b]) => nat_lit(a / b),
        ("Nat.gcd", [a, b]) => nat_lit(gcd(*a, *b)),
        ("Nat.land", [a, b]) => nat_lit(a & b),
        ("Nat.lor", [a, b]) => nat_lit(a | b),
        ("Nat.mod", [a, b]) => nat_lit(a % b),
        ("Nat.mul", [a, b]) => nat_lit(a * b),
        ("Nat.pow", [a, b]) => nat_lit(a.pow(u32::try_from(*b).expect("small exponent"))),
        ("Nat.pred", [a]) => nat_lit(a.saturating_sub(1)),
        ("Nat.shiftLeft", [a, b]) => nat_lit(a << b),
        ("Nat.shiftRight", [a, b]) => nat_lit(a >> b),
        ("Nat.sub", [a, b]) => nat_lit(a.saturating_sub(*b)),
        ("Nat.xor", [a, b]) => nat_lit(a ^ b),
        _ => panic!("no native value for {key} at {args:?}: extend `native` with the new carrier"),
    }
}

fn gcd(a: u64, b: u64) -> u64 {
    if b == 0 {
        a
    } else {
        gcd(b, a % b)
    }
}

/// The literals a carrier is applied to, one per leading binder (`Nat` or
/// `Int`), as numbers and as kernel values.
fn arguments(ty: &Expr) -> (Vec<u64>, Vec<Expr>) {
    let mut numbers = Vec::new();
    let mut values = Vec::new();
    let mut cursor = ty;
    while let ExprKind::Pi(_, domain, body) = cursor.kind() {
        let n = [7, 3][numbers.len()];
        let value = match erase(domain).kind() {
            ExprKind::Const(d, _) if d.to_string() == "Nat" => nat_lit(n),
            ExprKind::Const(d, _) if d.to_string() == "Int" => {
                int_lit(i64::try_from(n).expect("small"))
            }
            _ => panic!("a carrier's binders are Nat or Int: {ty}"),
        };
        numbers.push(n);
        values.push(value);
        cursor = body;
    }
    (numbers, values)
}

/// `e` with the wrappers around its root removed.
fn unwrapped(e: &Expr) -> &Expr {
    let mut e = e;
    while let ExprKind::MData(_, inner) = e.kind() {
        e = inner.as_ref();
    }
    e
}

fn applied(f: &Expr, args: &[Expr]) -> Expr {
    Expr::apps(f.clone(), args.iter().cloned())
}

/// The keys whose own type or value (hashed: a definition's or opaque's)
/// carries `MData`.
fn own_carriers(env: &Environment) -> BTreeSet<String> {
    EXTENSION_KEYS
        .iter()
        .map(|k| Name::from_string(k.name))
        .filter(|k| {
            env.get_const(k).is_some_and(|c| {
                let hashed = matches!(c.kind, ConstantKind::Definition | ConstantKind::Opaque);
                has_mdata(&c.type_) || (hashed && c.value.as_ref().is_some_and(has_mdata))
            }) && env.get_inductive(k).is_none()
                && env.get_constructor(k).is_none()
                && env.get_recursor(k).is_none()
        })
        .map(|k| k.to_string())
        .collect()
}

#[test]
fn test_fenced_kernel_reads_mdata_as_its_body_on_the_real_cones() {
    let env = load_key_modules(Environment::for_lean_replay());
    let carriers = own_carriers(&env);
    let want: BTreeSet<String> = CARRIERS.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(
        carriers, want,
        "the keys whose own type or value carries MData"
    );

    let targets: BTreeSet<Name> = CARRIERS.iter().map(|s| Name::from_string(s)).collect();
    let base = crate::reference_base_closed(&env, &targets, &ClosedRecheckOptions::default())
        .expect("the reference entry's empty base");
    assert!(
        base.report.passed() && base.entry_refusals.is_empty(),
        "{}\n{:?}",
        base.report.verdict_sentence(),
        base.entry_refusals
    );
    let kernel = base
        .into_kernel()
        .expect("every carrier's cone re-admitted");
    let tc = TypeChecker::new(kernel.environment());

    let mut unfold_carriers = BTreeSet::new();
    let mut wrapped_unfold_checks = 0;
    for key in CARRIERS {
        let name = Name::from_string(key);
        let info = env.get_const(&name).expect("carrier declared");
        let ty = &info.type_;
        let value = info.value.as_ref().expect("a carrier is a definition");
        assert!(
            has_mdata(ty) || has_mdata(value),
            "{key}: the type or value as Lean wrote it carries MData"
        );
        let bare = erase(value);
        let declared = erase(ty);
        let forms = [
            ("as written", value.clone()),
            ("erased", bare.clone()),
            ("wrapped everywhere", wrap_all(&bare)),
        ];
        let types = [
            ("as written", ty.clone()),
            ("erased", declared.clone()),
            ("wrapped everywhere", wrap_all(&declared)),
        ];

        // Checking and inference.
        let sort = tc.infer_type(&declared).expect("the erased type is typed");
        for (type_label, t) in &types {
            for (other_label, other) in &types {
                assert!(
                    tc.is_def_eq(t, other),
                    "{key}: type {type_label} == {other_label}"
                );
            }
            let s = tc
                .infer_type(t)
                .unwrap_or_else(|e| panic!("{key}: infer the type {type_label}: {e:?}"));
            assert!(
                tc.is_def_eq(&s, &sort),
                "{key}: type {type_label}: its sort"
            );
        }
        for (label, form) in &forms {
            for (type_label, t) in &types {
                kernel.check_closed_term(t, form).unwrap_or_else(|e| {
                    panic!("{key} {label}: check against the type {type_label}: {e:?}")
                });
            }
            let inferred = tc
                .infer_type(form)
                .unwrap_or_else(|e| panic!("{key} {label}: infer: {e:?}"));
            for (type_label, t) in &types {
                assert!(
                    tc.is_def_eq(&inferred, t),
                    "{key} {label}: inferred type == the type {type_label}"
                );
            }
        }
        let inferred_bare = erase(&tc.infer_type(&bare).expect("infer the erased value"));
        assert_eq!(
            erase(&tc.infer_type(value).expect("infer the written value")),
            inferred_bare,
            "{key}: inference commutes with erasure"
        );

        // Definitional equality.
        let constant = Expr::const_(name.clone(), Vec::new());
        for (label, form) in &forms {
            for (other_label, other) in &forms {
                assert!(tc.is_def_eq(form, other), "{key}: {label} == {other_label}");
            }
            assert!(
                tc.is_def_eq(form, &constant),
                "{key} {label}: δ to the constant"
            );
        }

        // The by-name extension's answer on literals is the native value.
        let (numbers, args) = arguments(&declared);
        let expected = native(key, &numbers);
        let by_name = tc.whnf(&applied(&constant, &args));
        assert!(
            !matches!(by_name.get_app_fn().kind(), ExprKind::Const(n, _) if *n == name),
            "{key}: the by-name extension fired: {by_name}"
        );
        assert!(
            tc.is_def_eq(&by_name, &expected),
            "{key}: by name, {by_name} is {expected}"
        );

        // whnf of the value applied to literals: equal up to erasure across
        // the forms, and (where the recursion is structural) the native value.
        let unfolds = UNFOLDS.contains(key);
        let bare_whnf = unfolds.then(|| erase(&tc.whnf(&applied(&bare, &args))));
        let wrong = match *key {
            "Nat.beq" | "Nat.ble" => bool_lit(expected == bool_lit(false)),
            k if k.starts_with("Int.") => int_lit(99),
            _ => nat_lit(99),
        };
        for bare_whnf in bare_whnf.as_slice() {
            unfold_carriers.insert(*key);
            for (label, form) in &forms {
                let reduced = tc.whnf(&applied(form, &args));
                assert_eq!(
                    &erase(&reduced),
                    bare_whnf,
                    "{key} {label}: whnf commutes with erasure"
                );
                assert!(
                    tc.is_def_eq(&reduced, &expected),
                    "{key} {label}: unfolds to the native value"
                );
                assert!(
                    !tc.is_def_eq(&reduced, &wrong),
                    "{key} {label}: negative control"
                );
            }
        }

        // Instantiation commutes with erasure: the type's codomain, and the
        // value's body where the value is a λ (`Nat.land`, `Nat.lor` and
        // `Nat.xor` are `Nat.bitwise` applied, with no binder of their own).
        let ExprKind::Pi(_, _, codomain) = unwrapped(ty).kind() else {
            panic!("{key}: a carrier's type is a Π");
        };
        let mut bodies = vec![("type", codomain)];
        if let ExprKind::Lam(_, _, body) = unwrapped(value).kind() {
            bodies.push(("value", body));
        }
        for (part, e) in bodies {
            assert_eq!(
                erase(&e.instantiate(&args[0])),
                erase(e).instantiate(&args[0]),
                "{key}: instantiating the {part} commutes with erasure"
            );
        }

        // A wrapper around any single node.
        for at in 0..node_count(&bare) {
            let form = wrap_at(&bare, at);
            kernel
                .check_closed_term(ty, &form)
                .unwrap_or_else(|e| panic!("{key}: wrapper at node {at}: {e:?}"));
            assert!(tc.is_def_eq(&form, &bare), "{key}: wrapper at node {at}");
            for bare_whnf in bare_whnf.as_slice() {
                wrapped_unfold_checks += 1;
                assert_eq!(
                    &erase(&tc.whnf(&applied(&form, &args))),
                    bare_whnf,
                    "{key}: wrapper at node {at}: whnf"
                );
            }
        }
        for at in 0..node_count(&declared) {
            let t = wrap_at(&declared, at);
            kernel
                .check_closed_term(&t, &bare)
                .unwrap_or_else(|e| panic!("{key}: type wrapper at node {at}: {e:?}"));
            assert!(
                tc.is_def_eq(&t, &declared),
                "{key}: type wrapper at node {at}"
            );
        }
    }
    let expected_unfolds: BTreeSet<&str> = UNFOLDS.iter().copied().collect();
    assert!(
        !expected_unfolds.is_empty(),
        "structural carriers are exercised"
    );
    assert_eq!(
        unfold_carriers, expected_unfolds,
        "every structural carrier was checked"
    );
    assert!(
        wrapped_unfold_checks > 0,
        "structural node wrappers were checked"
    );
}

/// Whether the fingerprint of `key` reads an ordinary constant whose type or
/// hashed value carries `MData`: the fingerprint's walk (references of every
/// hashed expression; a family member stands for its block's input, whose
/// wrappers are kept), written out independently.
fn ordinary_cone_carries_mdata(env: &Environment, key: &Name) -> bool {
    let family_of = |name: &Name| {
        env.get_inductive(name)
            .or_else(|| {
                env.get_constructor(name)
                    .and_then(|c| env.get_inductive(&c.inductive_name))
            })
            .or_else(|| {
                env.get_recursor(name)
                    .and_then(|r| env.get_inductive(&r.inductive_name))
            })
    };
    let mut seen: BTreeSet<Name> = BTreeSet::new();
    let mut stack = vec![key.clone()];
    while let Some(name) = stack.pop() {
        if !seen.insert(name.clone()) {
            continue;
        }
        let mut read: Vec<&Expr> = Vec::new();
        if let Some(ind) = family_of(&name) {
            let members = if ind.all_names.is_empty() {
                vec![ind.name.clone()]
            } else {
                ind.all_names.clone()
            };
            for member in &members {
                seen.insert(member.clone());
                let Some(m) = env.get_inductive(member) else {
                    continue;
                };
                read.push(&m.type_);
                for ctor in &m.constructor_names {
                    seen.insert(ctor.clone());
                    if let Some(c) = env.get_constructor(ctor) {
                        read.push(&c.type_);
                    }
                }
            }
        } else if let Some(c) = env.get_const(&name) {
            let hashed = matches!(c.kind, ConstantKind::Definition | ConstantKind::Opaque);
            if has_mdata(&c.type_) || (hashed && c.value.as_ref().is_some_and(has_mdata)) {
                return true;
            }
            read.push(&c.type_);
            if let (true, Some(v)) = (hashed, c.value.as_ref()) {
                read.push(v);
            }
        }
        for e in read {
            let mut walk = vec![e];
            while let Some(x) = walk.pop() {
                match x.kind() {
                    ExprKind::Const(n, _) | ExprKind::Proj(n, _, _) => stack.push(n.clone()),
                    _ => {}
                }
                walk.extend(children(x));
            }
        }
    }
    false
}

/// The erasure moves a key's fingerprint exactly when the key's ordinary cone
/// carries a wrapper: the rows the re-pin of 2026-11-14 moved, and no other.
#[test]
fn test_binding_fingerprint_moves_exactly_where_an_ordinary_cone_carries_mdata() {
    let env = load_key_modules(Environment::for_lean_replay());
    let mut erased = Fingerprinter::new(&env);
    let mut kept = Fingerprinter::keeping_annotations(&env);
    let mut moved = BTreeSet::new();
    for key in EXTENSION_KEYS.iter().map(|k| Name::from_string(k.name)) {
        assert!(declares(&env, &key), "v4.30 declares {key}");
        let differs = erased.constant(&key) != kept.constant(&key);
        assert_eq!(
            differs,
            ordinary_cone_carries_mdata(&env, &key),
            "{key}: the fingerprint moves iff its ordinary cone carries MData"
        );
        if differs {
            moved.insert(key.to_string());
        }
    }
    assert!(
        CARRIERS.iter().all(|c| moved.contains(*c)),
        "every carrier moved: {moved:?}"
    );
    eprintln!("keys the erasure moved: {moved:?}");
}
