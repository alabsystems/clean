// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Root arity guard for native reducers (`reduce_native` /
//! `native_reducer_arity`): a reducer computes the value of its constant at the
//! constant's own arity, and an OVER-APPLIED term must re-apply the surplus,
//! never drop it.
//!
//! Before the guard, `reduce_ite` (and every `… → α` reducer) returned its
//! branch built from `args[3]`/`args[4]` while `reduce_native` passed the whole
//! spine and re-applied nothing, so `@ite (Nat → Prop) True (isTrue …) P Q 0`
//! reduced to `P` — the trailing `0` DROPPED. Then `ite … 0` and `ite … 1`
//! were judged def-eq, and a closed proof of `False` kernel-checked with an
//! EMPTY axiom closure. These tests pin that the forged `False` is now refused
//! and that a legitimately over-applied `ite`/`dite` still reduces, with the
//! surplus re-applied.

use crate::env::{Declaration, Environment};
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn c(name: &str) -> Expr {
    Expr::const_(Name::from_string(name), vec![])
}

fn nat() -> Expr {
    c("Nat")
}

/// `@ite.{1} α cond inst then_ else_` — `α : Sort 1` (a `Type`).
fn ite_at(alpha: &Expr, cond: &Expr, inst: &Expr, then_: &Expr, else_: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("ite"), vec![Level::succ(Level::zero())]),
        [
            alpha.clone(),
            cond.clone(),
            inst.clone(),
            then_.clone(),
            else_.clone(),
        ],
    )
}

/// `Decidable.isTrue True True.intro : Decidable True`.
fn dec_true() -> Expr {
    Expr::apps(c("Decidable.isTrue"), [c("True"), c("True.intro")])
}

/// `@Eq.{1} Nat a b`.
fn eq_nat(a: &Expr, b: &Expr) -> Expr {
    Expr::apps(
        Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]),
        [nat(), a.clone(), b.clone()],
    )
}

/// The forged `False`: an over-applied `ite` at a function-valued carrier.
///
/// `A := Nat → Prop`, `P := fun n => n = 0`, `ITE := @ite A True (isTrue) P Q`.
/// `ITE 0` and `ITE 1` (over-applications) are transported into each other and
/// `Nat.ne_of_beq_false 1 0 … : 1 = 0 → False` closes it. Every constant is a
/// real prelude constant, so the term's axiom closure is empty; the ONLY thing
/// that lets it type-check is `ITE 0 ≡ ITE 1`, which the dropped-argument bug
/// produced and the arity guard forbids.
fn forged_false_value() -> Expr {
    let one = Level::succ(Level::zero());
    let two = Level::succ(one.clone());
    let a_ty = Expr::pi(BinderInfo::Default, nat(), Expr::sort(Level::zero())); // Nat → Prop
    let p = Expr::lam(
        BinderInfo::Default,
        nat(),
        eq_nat(&Expr::bvar(0), &Expr::nat_lit(0)),
    ); // fun n => n = 0
    let q = Expr::lam(BinderInfo::Default, nat(), c("False"));
    let ite = ite_at(&a_ty, &c("True"), &dec_true(), &p, &q); // : Nat → Prop
    let t0 = Expr::app(ite.clone(), Expr::nat_lit(0));
    let t1 = Expr::app(ite.clone(), Expr::nat_lit(1));

    // hpos1 : @Eq.{1} A ITE P  (accepted only while ITE ≡ P).
    let eq_a = |l: &Expr, r: &Expr| {
        Expr::apps(
            Expr::const_(Name::from_string("Eq"), vec![one.clone()]),
            [a_ty.clone(), l.clone(), r.clone()],
        )
    };
    let hpos1 = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
        [a_ty.clone(), p.clone()],
    );
    // Eq.rec.{motive_level, type_level} = Eq.rec.{0, 1} here.
    let eqrec = Expr::const_(
        Name::from_string("Eq.rec"),
        vec![Level::zero(), one.clone()],
    );

    // h0 : ITE 0, via Eq.rec with motive `fun b _ => b 0 → ITE 0`, transported
    // from P back to ITE, applied to `Eq.refl Nat 0 : P 0`.
    let motive0 = Expr::lam(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::lam(
            BinderInfo::Default,
            eq_a(&ite, &Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                Expr::app(Expr::bvar(1), Expr::nat_lit(0)),
                t0.clone(),
            ),
        ),
    );
    let id0 = Expr::lam(BinderInfo::Default, t0.clone(), Expr::bvar(0));
    let to0 = Expr::apps(
        eqrec.clone(),
        [
            a_ty.clone(),
            ite.clone(),
            motive0,
            id0,
            p.clone(),
            hpos1.clone(),
        ],
    );
    let refl00 = Expr::apps(
        Expr::const_(Name::from_string("Eq.refl"), vec![one.clone()]),
        [nat(), Expr::nat_lit(0)],
    );
    let h0 = Expr::app(to0, refl00);
    // Re-type h0 : ITE 0 as ITE 1 (accepted only while ITE 0 ≡ ITE 1).
    let h0p = Expr::app(
        Expr::lam(BinderInfo::Default, t1.clone(), Expr::bvar(0)),
        h0,
    );

    // h1 : P 1  (= Eq Nat 1 0), via Eq.rec with motive `fun b _ => ITE 1 → b 1`.
    let motive1 = Expr::lam(
        BinderInfo::Default,
        a_ty.clone(),
        Expr::lam(
            BinderInfo::Default,
            eq_a(&ite, &Expr::bvar(0)),
            Expr::pi(
                BinderInfo::Default,
                t1.clone(),
                Expr::app(Expr::bvar(2), Expr::nat_lit(1)),
            ),
        ),
    );
    let id1 = Expr::lam(BinderInfo::Default, t1.clone(), Expr::bvar(0));
    let to1 = Expr::apps(
        eqrec,
        [a_ty.clone(), ite.clone(), motive1, id1, p.clone(), hpos1],
    );
    let h1 = Expr::app(to1, h0p);

    // False := Nat.ne_of_beq_false 1 0 (Eq.refl Bool (Nat.beq 1 0)) h1.
    let beq10 = Expr::apps(c("Nat.beq"), [Expr::nat_lit(1), Expr::nat_lit(0)]);
    let refl_beq = Expr::apps(
        Expr::const_(
            Name::from_string("Eq.refl"),
            vec![Level::succ(Level::zero())],
        ),
        [c("Bool"), beq10],
    );
    let _ = two;
    Expr::apps(
        c("Nat.ne_of_beq_false"),
        [Expr::nat_lit(1), Expr::nat_lit(0), refl_beq, h1],
    )
}

/// The forged `False` must be REFUSED by `add_decl` (it type-checked with an
/// empty axiom closure before the arity guard).
fn assert_forged_false_refused(env: &Environment) {
    let mut env = env.clone();
    let name = Name::from_string("e4n_ite_overapp_false");
    let result = env.add_decl(Declaration::Theorem {
        name: name.clone(),
        level_params: vec![],
        type_: c("False"),
        value: forged_false_value(),
    });
    assert!(
        result.is_err(),
        "the over-applied-ite False must be refused; it was accepted before the arity guard"
    );
    assert!(
        env.get_const(&name).is_none(),
        "a refused theorem must leave no declaration"
    );
}

#[test]
fn over_applied_ite_false_is_refused_with_prelude() {
    let env = Environment::with_prelude();
    assert_forged_false_refused(&env);
}

/// A legitimately over-applied `ite` at a FUNCTION carrier still reduces, with
/// the surplus argument re-applied: `(if True then f else g) 0` ≡ `f 0` and
/// `≢ g 0`.
#[test]
fn over_applied_ite_reduces_and_reapplies() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let nat_to_nat = Expr::pi(BinderInfo::Default, nat(), nat());
    let f = Expr::lam(
        BinderInfo::Default,
        nat(),
        Expr::app(c("Nat.succ"), Expr::bvar(0)),
    ); // fun n => n+1
    let g = Expr::lam(BinderInfo::Default, nat(), Expr::bvar(0)); // fun n => n
    let ite = ite_at(&nat_to_nat, &c("True"), &dec_true(), &f, &g); // : Nat → Nat
    let applied = Expr::app(ite, Expr::nat_lit(0)); // (if True then f else g) 0
    let f0 = Expr::app(f.clone(), Expr::nat_lit(0));
    let g0 = Expr::app(g.clone(), Expr::nat_lit(0));
    assert!(
        tc.is_def_eq(&applied, &f0),
        "(if True then f else g) 0 must reduce to f 0 (the surplus 0 re-applied to the then-branch)"
    );
    assert!(
        !tc.is_def_eq(&applied, &g0),
        "it must NOT equal g 0: the else-branch is not selected"
    );
    // Direct evidence the surplus was re-applied, not dropped: the reducer's
    // native output is an application, not the bare branch `f`.
    let reduced = tc
        .try_reduce_native(&Expr::app(
            ite_at(&nat_to_nat, &c("True"), &dec_true(), &f, &g),
            Expr::nat_lit(0),
        ))
        .expect("over-applied ite reduces natively");
    assert!(
        matches!(reduced.kind(), ExprKind::App(_, _)),
        "the native result must re-apply the surplus argument (an App), got {reduced:?}"
    );
}

/// `dite` shares the shape: an over-applied `dite` at a function carrier
/// re-applies its surplus argument to the taken branch (the branch receives the
/// decidability proof, then the surplus).
#[test]
fn over_applied_dite_reapplies() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    let nat_to_nat = Expr::pi(BinderInfo::Default, nat(), nat());
    // then_ : True → (Nat → Nat) := fun _ => Nat.succ ; else_ : ¬True → (Nat → Nat)
    let then_ = Expr::lam(BinderInfo::Default, c("True"), c("Nat.succ"));
    let not_true = Expr::pi(BinderInfo::Default, c("True"), c("False"));
    let else_ = Expr::lam(BinderInfo::Default, not_true, c("Nat.succ"));
    let dite = Expr::apps(
        Expr::const_(Name::from_string("dite"), vec![Level::succ(Level::zero())]),
        [nat_to_nat, c("True"), dec_true(), then_, else_],
    ); // : Nat → Nat
    let applied = Expr::app(dite, Expr::nat_lit(0)); // (dite …) 0
    let want = Expr::app(c("Nat.succ"), Expr::nat_lit(0)); // Nat.succ 0
    assert!(
        tc.is_def_eq(&applied, &want),
        "over-applied dite must reduce to (then_ proof) 0 = Nat.succ 0, surplus re-applied"
    );
}

/// The arity `reduce_native` derives is the constant's declared leading-`Pi`
/// count: `ite`/`dite` are 5, and a base-valued reducer is its true arity.
#[test]
fn native_reducer_arity_is_the_declared_pi_count() {
    let env = Environment::with_prelude();
    let tc = TypeChecker::new(&env);
    assert_eq!(tc.native_reducer_arity(&Name::from_string("ite")), Some(5));
    assert_eq!(tc.native_reducer_arity(&Name::from_string("dite")), Some(5));
    // `Nat.add : Nat → Nat → Nat` — arity 2, result not a function.
    assert_eq!(
        tc.native_reducer_arity(&Name::from_string("Nat.add")),
        Some(2)
    );
    // Absent head: no arity can be derived.
    assert_eq!(
        tc.native_reducer_arity(&Name::from_string("Not.A.Real.Constant")),
        None
    );
}
