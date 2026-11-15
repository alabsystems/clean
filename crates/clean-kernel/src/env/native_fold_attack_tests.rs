// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! ATTACKS on name-keyed kernel rules (`docs/issues/2026-09-26-kernel-native-
//! fold-by-name.md`). Each test states a proof the kernel must REFUSE, and
//! each was ACCEPTED before native-fold authority (`native_fold_authority.rs`):
//! a rule keyed on a constant's NAME fired for whatever the environment said
//! that name meant. Every attack has a positive control showing the canonical
//! constant still computes.
//!
//! Written against the kernel's public surface only (`add_decl`,
//! `TypeChecker::check_type`), so the same file compiles on the pre-authority
//! kernel and is the RED half of the RED/GREEN evidence.

use crate::env::{Declaration, EnvError, Environment};
use crate::expr::{BinderInfo, Expr};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

fn n(s: &str) -> Name {
    Name::from_string(s)
}

fn c(s: &str) -> Expr {
    Expr::const_(n(s), vec![])
}

fn one() -> Level {
    Level::succ(Level::zero())
}

fn nat() -> Expr {
    c("Nat")
}

fn lit(v: u64) -> Expr {
    Expr::nat_lit(v)
}

fn lam(ty: Expr, body: Expr) -> Expr {
    Expr::lam(BinderInfo::Default, ty, body)
}

fn pi(ty: Expr, body: Expr) -> Expr {
    Expr::pi(BinderInfo::Default, ty, body)
}

/// `@Eq.{1} ty a b`.
fn eq(ty: Expr, a: Expr, b: Expr) -> Expr {
    Expr::apps(Expr::const_(n("Eq"), vec![one()]), [ty, a, b])
}

/// `@Eq.refl.{1} ty a`.
fn refl(ty: Expr, a: Expr) -> Expr {
    Expr::apps(Expr::const_(n("Eq.refl"), vec![one()]), [ty, a])
}

/// Does `rfl : lhs = rhs` (at `ty`) kernel-check?
fn rfl_checks(env: &Environment, ty: Expr, lhs: Expr, rhs: Expr) -> bool {
    rfl_result(env, ty, lhs, rhs).is_ok()
}

/// `rfl : lhs = rhs`, with the kernel's error when it does not check.
fn rfl_result(env: &Environment, ty: Expr, lhs: Expr, rhs: Expr) -> Result<(), String> {
    let tc = TypeChecker::new(env);
    tc.check_type(&refl(ty.clone(), rhs.clone()), &eq(ty, lhs, rhs))
        .map(|_| ())
        .map_err(|e| format!("{e:?}"))
}

fn def(env: &mut Environment, name: &str, ty: Expr, value: Expr) -> Result<(), EnvError> {
    env.add_decl(Declaration::Definition {
        name: n(name),
        level_params: vec![],
        type_: ty,
        value,
        is_reducible: true,
    })
}

fn axiom(env: &mut Environment, name: &str, ty: Expr) -> Result<(), EnvError> {
    env.add_decl(Declaration::Axiom {
        name: n(name),
        level_params: vec![],
        type_: ty,
    })
}

fn theorem(env: &mut Environment, name: &str, ty: Expr, value: Expr) -> Result<(), EnvError> {
    env.add_decl(Declaration::Theorem {
        name: n(name),
        level_params: vec![],
        type_: ty,
        value,
    })
}

fn nat2() -> Expr {
    pi(nat(), pi(nat(), nat()))
}

/// Crystal E4c, end to end: `Nat.gcd := fun _ _ => 0` in `with_prelude` (which
/// does not declare `Nat.gcd`), `gcd x y = 0` by δ, `gcd 4 6 = 2` by the
/// fold, `2 = 0` by `Eq.trans`, `False` by `congrArg`/`Eq.mp`. Every step
/// returned `Ok` at `d57e0e018`.
#[test]
fn attack_e4c_user_gcd_chain_to_false() {
    let mut env = Environment::with_prelude();
    assert!(env.get_const(&n("Nat.gcd")).is_none());
    def(
        &mut env,
        "Nat.gcd",
        nat2(),
        lam(nat(), lam(nat(), c("Nat.zero"))),
    )
    .expect("user Nat.gcd");
    let gcd_xy = Expr::apps(c("Nat.gcd"), [Expr::bvar(1), Expr::bvar(0)]);
    theorem(
        &mut env,
        "e4c_gcd_zero",
        pi(nat(), pi(nat(), eq(nat(), gcd_xy, lit(0)))),
        lam(nat(), lam(nat(), refl(nat(), lit(0)))),
    )
    .expect("δ-unfolding the user's definition is legitimate");
    let gcd_4_6 = Expr::apps(c("Nat.gcd"), [lit(4), lit(6)]);
    // Step 3, the fold (recorded; asserted below with the rest of the chain).
    let fold_accepted = rfl_checks(&env, nat(), gcd_4_6.clone(), lit(2));
    let h20 = Expr::apps(
        Expr::const_(n("Eq.trans"), vec![one()]),
        [
            nat(),
            lit(2),
            gcd_4_6,
            lit(0),
            refl(nat(), lit(2)),
            Expr::apps(c("e4c_gcd_zero"), [lit(4), lit(6)]),
        ],
    );
    let p = lam(
        nat(),
        Expr::apps(
            Expr::const_(n("Nat.rec"), vec![one()]),
            [
                lam(nat(), Expr::prop()),
                c("False"),
                lam(nat(), lam(Expr::prop(), c("True"))),
                Expr::bvar(0),
            ],
        ),
    );
    let congr = Expr::apps(
        Expr::const_(n("congrArg"), vec![one(), one()]),
        [nat(), Expr::prop(), lit(2), lit(0), p.clone(), h20],
    );
    let false_proof = Expr::apps(
        Expr::const_(n("Eq.mp"), vec![Level::zero()]),
        [
            Expr::app(p.clone(), lit(2)),
            Expr::app(p, lit(0)),
            congr,
            c("True.intro"),
        ],
    );
    let false_accepted = theorem(&mut env, "e4c_false", c("False"), false_proof).is_ok();
    assert!(
        !fold_accepted && !false_accepted,
        "ATTACK ACCEPTED: Nat.gcd 4 6 = 2 by rfl: {fold_accepted}; e4c_false : False: {false_accepted}"
    );
    // Positive control: the δ answer, which the fold used to contradict.
    let gcd_4_6 = Expr::apps(c("Nat.gcd"), [lit(4), lit(6)]);
    assert!(rfl_checks(&env, nat(), gcd_4_6, lit(0)));
}

/// An AXIOM has no computational content: a user axiom `Nat.gcd` must not
/// fold. Accepted before by name.
#[test]
fn attack_user_axiom_gcd_computes() {
    let mut env = Environment::with_prelude();
    axiom(&mut env, "Nat.gcd", nat2()).expect("user axiom");
    assert!(
        !rfl_checks(
            &env,
            nat(),
            Expr::apps(c("Nat.gcd"), [lit(4), lit(6)]),
            lit(2)
        ),
        "ATTACK ACCEPTED: an axiom computed"
    );
}

/// `Nat.shiftRight` as the value-less AXIOM the bare `init_nat` path installs
/// computed `8 >>> 1 = 4` by name.
#[test]
fn attack_shiftright_axiom_computes() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    assert_eq!(
        env.get_const(&n("Nat.shiftRight")).map(|ci| ci.kind),
        Some(crate::env::ConstantKind::Axiom)
    );
    assert!(
        !rfl_checks(
            &env,
            nat(),
            Expr::apps(c("Nat.shiftRight"), [lit(8), lit(1)]),
            lit(4)
        ),
        "ATTACK ACCEPTED: the Nat.shiftRight axiom computed"
    );
    // Positive control: a canonical fold in the same environment.
    assert!(rfl_checks(
        &env,
        nat(),
        Expr::apps(c("Nat.add"), [lit(8), lit(1)]),
        lit(9)
    ));
}

/// A registered native reducer fired for a head the user defined: with
/// `String.startsWith := fun _ _ => true`, the reducer said `false`.
#[test]
fn attack_user_registry_head_fires() {
    let mut env = Environment::with_prelude();
    assert!(env.get_const(&n("String.startsWith")).is_none());
    let string = c("String");
    let bool_ = c("Bool");
    def(
        &mut env,
        "String.startsWith",
        pi(string.clone(), pi(string.clone(), bool_.clone())),
        lam(string.clone(), lam(string, c("Bool.true"))),
    )
    .expect("user String.startsWith");
    let app = Expr::apps(
        c("String.startsWith"),
        [Expr::str_lit("a"), Expr::str_lit("b")],
    );
    assert!(
        !rfl_checks(&env, bool_.clone(), app.clone(), c("Bool.false")),
        "ATTACK ACCEPTED: the String.startsWith reducer overrode the user's definition"
    );
    assert!(rfl_checks(&env, bool_, app, c("Bool.true")), "δ answer");
}

/// The `HAdd.hAdd` short-circuit dispatched on the instance's NAME: a user
/// `instHAddNatNatNat` (absent from `with_prelude`) whose `hAdd` is constantly
/// zero was computed as `Nat.add`.
#[test]
fn attack_user_instance_name_dispatch() {
    let mut env = Environment::with_prelude();
    assert!(env.get_const(&n("instHAddNatNatNat")).is_none());
    let zero3 = vec![Level::zero(), Level::zero(), Level::zero()];
    let hadd_nat = Expr::apps(
        Expr::const_(n("HAdd"), zero3.clone()),
        [nat(), nat(), nat()],
    );
    let inst = Expr::apps(
        Expr::const_(n("HAdd.mk"), zero3.clone()),
        [nat(), nat(), nat(), lam(nat(), lam(nat(), c("Nat.zero")))],
    );
    def(&mut env, "instHAddNatNatNat", hadd_nat, inst).expect("user instance");
    let sum = Expr::apps(
        Expr::const_(n("HAdd.hAdd"), zero3),
        [nat(), nat(), nat(), c("instHAddNatNatNat"), lit(2), lit(2)],
    );
    assert!(
        !rfl_checks(&env, nat(), sum.clone(), lit(4)),
        "ATTACK ACCEPTED: HAdd.hAdd computed Nat.add through a user instance"
    );
    assert!(rfl_checks(&env, nat(), sum, lit(0)), "δ answer");
}

/// The `HAppend.hAppend` reducer concatenated two string literals WHATEVER the
/// instance: a second `HAppend String String String` instance whose `hAppend`
/// keeps its first argument reduced `"a" ++ "b"` to `"ab"`. This one needed no
/// missing name — it worked in every environment.
#[test]
fn attack_happend_ignores_its_instance() {
    let mut env = Environment::with_prelude();
    let string = c("String");
    let zero3 = vec![Level::zero(), Level::zero(), Level::zero()];
    let happend_s = Expr::apps(
        Expr::const_(n("HAppend"), zero3.clone()),
        [string.clone(), string.clone(), string.clone()],
    );
    let inst = Expr::apps(
        Expr::const_(n("HAppend.mk"), zero3.clone()),
        [
            string.clone(),
            string.clone(),
            string.clone(),
            lam(string.clone(), lam(string.clone(), Expr::bvar(1))),
        ],
    );
    def(&mut env, "keepFirstAppend", happend_s, inst).expect("user instance");
    let app = |inst: Expr| {
        Expr::apps(
            Expr::const_(n("HAppend.hAppend"), zero3.clone()),
            [
                string.clone(),
                string.clone(),
                string.clone(),
                inst,
                Expr::str_lit("a"),
                Expr::str_lit("b"),
            ],
        )
    };
    assert!(
        !rfl_checks(
            &env,
            string.clone(),
            app(c("keepFirstAppend")),
            Expr::str_lit("ab")
        ),
        "ATTACK ACCEPTED: HAppend.hAppend ignored its instance"
    );
    assert!(
        rfl_checks(
            &env,
            string.clone(),
            app(c("keepFirstAppend")),
            Expr::str_lit("a")
        ),
        "δ answer"
    );
    // Positive control: the canonical instance still concatenates.
    let canonical = app(c("instHAppendString"));
    assert!(rfl_checks(&env, string, canonical, Expr::str_lit("ab")));
}

/// `Lean.reduceBool c ≡ c` is the rule of the canonical `opaque
/// Lean.reduceBool (b : Bool) : Bool := b`; `with_prelude` does not declare it,
/// and for a user's `Lean.reduceBool := fun _ => true` the rule equated
/// `false` with `true`.
#[test]
fn attack_user_reduce_bool() {
    let mut env = Environment::with_prelude();
    assert!(env.get_const(&n("Lean.reduceBool")).is_none());
    let bool_ = c("Bool");
    def(
        &mut env,
        "Lean.reduceBool",
        pi(bool_.clone(), bool_.clone()),
        lam(bool_.clone(), c("Bool.true")),
    )
    .expect("user Lean.reduceBool");
    let app = Expr::app(c("Lean.reduceBool"), c("Bool.false"));
    assert!(
        !rfl_checks(&env, bool_.clone(), app.clone(), c("Bool.false")),
        "ATTACK ACCEPTED: Lean.reduceBool's rule fired for a user definition"
    );
    assert!(rfl_checks(&env, bool_, app, c("Bool.true")), "δ answer");
}

/// The quotient rule fired for a `Quot.lift` / `Quot.mk` a user declared in an
/// environment whose quotient was never initialized: `Quot.lift … (Quot.mk …
/// 0)` reduced to `f 0` while the user's `Quot.lift` δ-reduces to
/// `f (succ (Quot.mk … 0))`.
#[test]
fn attack_user_quotient_rule() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    env.init_eq().expect("init_eq");
    assert!(
        env.get_quot(&n("Quot.mk")).is_none(),
        "quotient not initialized"
    );
    let rel = pi(nat(), pi(nat(), Expr::prop()));
    axiom(
        &mut env,
        "Quot.mk",
        pi(Expr::type_(), pi(rel.clone(), pi(nat(), nat()))),
    )
    .expect("user Quot.mk");
    // Quot.lift : (α : Type) → (r) → (β : Type) → (f : Nat → Nat) → (h : Nat) → (q : Nat) → Nat
    //           := fun α r β f h q => f (Nat.succ q)
    let lift_ty = pi(
        Expr::type_(),
        pi(
            rel.clone(),
            pi(
                Expr::type_(),
                pi(pi(nat(), nat()), pi(nat(), pi(nat(), nat()))),
            ),
        ),
    );
    let lift_val = lam(
        Expr::type_(),
        lam(
            rel.clone(),
            lam(
                Expr::type_(),
                lam(
                    pi(nat(), nat()),
                    lam(
                        nat(),
                        lam(
                            nat(),
                            Expr::app(Expr::bvar(2), Expr::app(c("Nat.succ"), Expr::bvar(0))),
                        ),
                    ),
                ),
            ),
        ),
    );
    def(&mut env, "Quot.lift", lift_ty, lift_val).expect("user Quot.lift");
    let r = lam(nat(), lam(nat(), eq(nat(), Expr::bvar(1), Expr::bvar(0))));
    let mk0 = Expr::apps(c("Quot.mk"), [nat(), r.clone(), lit(0)]);
    let lifted = Expr::apps(
        c("Quot.lift"),
        [
            nat(),
            r,
            nat(),
            lam(nat(), Expr::bvar(0)),
            lit(0),
            mk0.clone(),
        ],
    );
    assert!(
        !rfl_checks(&env, nat(), lifted.clone(), lit(0)),
        "ATTACK ACCEPTED: the quotient rule fired for a user Quot.lift"
    );
    let delta = rfl_result(&env, nat(), lifted, Expr::app(c("Nat.succ"), mk0));
    assert!(delta.is_ok(), "δ answer: {delta:?}");
}

/// A string literal's expansion `String.ofList [Char.ofNat c, …]` is its
/// meaning only over the canonical `Char.ofNat`. With a user `Char.ofNat`
/// that forgets its argument, `"a"` and `"b"` expanded to one term.
#[test]
fn attack_string_literal_expansion_over_user_char_of_nat() {
    let mut env = Environment::with_prelude();
    // The user's `Char.ofNat` forgets its argument: it is the canonical one
    // applied to 122 ('z') whatever it is given.
    let canonical = env
        .get_const(&n("Char.ofNat"))
        .and_then(|ci| ci.value.clone())
        .expect("with_prelude defines Char.ofNat");
    assert!(
        env.forget_decl(&n("Char.ofNat")),
        "simulate an environment without Char.ofNat"
    );
    def(
        &mut env,
        "Char.ofNat",
        pi(nat(), c("Char")),
        lam(nat(), Expr::app(canonical, lit(122))),
    )
    .expect("user Char.ofNat");
    let string = c("String");
    let list_b = Expr::apps(
        Expr::const_(n("List.cons"), vec![Level::zero()]),
        [
            c("Char"),
            Expr::app(c("Char.ofNat"), lit(98)),
            Expr::app(Expr::const_(n("List.nil"), vec![Level::zero()]), c("Char")),
        ],
    );
    let b_spelled = Expr::app(c("String.ofList"), list_b);
    assert!(
        !rfl_checks(&env, string, Expr::str_lit("a"), b_spelled),
        "ATTACK ACCEPTED: \"a\" = String.ofList [Char.ofNat 98] through a user Char.ofNat"
    );
}

/// `char_code_point` read the WIDTH of `@BitVec.ofFin w ⟨v, _⟩` (and the
/// BOUND of `@Fin.mk n v _`) instead of the value: a character with a
/// bare-literal width 32 read as code point 32.
#[test]
fn attack_char_code_point_reads_width() {
    let fin = Expr::apps(c("Fin.mk"), [lit(1 << 32), lit(65), c("trivial")]);
    let bv = Expr::apps(c("BitVec.ofFin"), [lit(32), fin]);
    let ch = Expr::apps(
        c("Char.mk"),
        [Expr::app(c("UInt32.ofBitVec"), bv), c("trivial")],
    );
    assert_eq!(
        super::native_reducers_char::char_code_point(&ch),
        Some(65),
        "ATTACK ACCEPTED: the code point was read from the width or the bound"
    );
}
