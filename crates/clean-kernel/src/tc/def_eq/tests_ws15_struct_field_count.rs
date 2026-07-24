// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! WS15 triage repro + soundness pins — the real-Mathlib "Type mismatch /
//! NotAFunction (head: Preorder)" family.
//!
//! ## What the triage found
//!
//! On real Mathlib (`Mathlib/Data/Nat/Basic`, `Mathlib/Order/Basic`,
//! `Mathlib/Algebra/Group/Defs`) the dominant residual "Type mismatch" /
//! "Expected function type" failures all reduce to ONE root, observed with the
//! WS15 term diagnostic:
//!
//! ```text
//! WS15-NAF f=Preorder.mk {0} Nat (LE.mk {0} Nat Nat.le) (LT.mk {0} Nat Nat.lt)
//!              Nat.le_refl Nat.le_trans
//!          | f_ty = Preorder Nat | f_ty_whnf = Preorder Nat
//!          | arg = Nat.lt_iff_le_and_not_ge
//! ```
//!
//! Lean's `class Preorder α extends LE α, LT α where le_refl; le_trans;
//! lt := …; lt_iff_le_not_ge` has FIVE constructor fields
//! (`toLE, toLT, le_refl, le_trans, lt_iff_le_not_ge`). Clean's imported
//! `Preorder.mk` accepts only FOUR — the auto-bound default-proof field
//! `lt_iff_le_not_ge` was dropped during `.olean` structure import. So
//! `Preorder.mk … le_trans` is already saturated at type `Preorder α`, and the
//! genuine FIFTH-field application is (correctly!) rejected as `NotAFunction`.
//! `Nat.instLinearOrder` / `Prod.instPreorder` / `Pi.preorder` / … all fail
//! this way, get masked to axioms, and then every `Preorder.toLE (…)` chain
//! through them stays stuck — cascading into the `Pi vs Iff`,
//! `Decidable vs Decidable`, `LE.le vs And` and hundreds of `Unknown constant`
//! downstream failures.
//!
//! ## Why this is NOT a `tc/` def-eq gap
//!
//! The kernel is behaving *correctly*: a constructor application saturated at
//! its declared field count has the inductive type (not a function type), so a
//! further application MUST be rejected. The defect is the imported structure's
//! field count (a `clean-olean` / `clean-mathverse` import concern), not kernel
//! def-eq incompleteness. There is no sound `tc/` change that closes it — making
//! `S α` (a structure *type*) compare def-eq to `… → S α`, or fabricating a
//! constructor field that was never declared, would be unsound.
//!
//! These tests therefore (a) reproduce the exact saturated-constructor /
//! `NotAFunction` shape the triage observed, (b) pin that the kernel keeps the
//! sound boundary, and (c) confirm that when a parent-`extends` structure IS
//! registered with its full field set the parent-projection chain reduces — so
//! the kernel is demonstrably not the gap.

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::name::Name;
use crate::tc::TypeChecker;

/// Register a one-field "carrier" structure `Carrier α` with constructor
/// `Carrier.mk : (α : Type) → (op : α → α → α) → Carrier α`.
///
/// This is the faithful stand-in for Lean's `Mul`/`LE` parent classes: a
/// single-field structure whose field is a function type. The structure *type*
/// `Carrier α` must never be definitionally equal to its field type
/// `α → α → α`.
fn add_carrier(env: &mut Environment) {
    let carrier = Name::from_string("Carrier");
    // Carrier : Type → Type
    let carrier_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // op field type, under the α binder: α → α → α
    let op_ty = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
        Expr::pi(BinderInfo::Default, Expr::bvar(1), Expr::bvar(2)),
    );
    // Carrier.mk : (α : Type) → (op : α → α → α) → Carrier α
    let carrier_app = Expr::app(Expr::const_(carrier.clone(), vec![]), Expr::bvar(1));
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(BinderInfo::Default, op_ty, carrier_app),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: carrier,
            type_: carrier_type,
            constructors: vec![Constructor {
                name: Name::from_string("Carrier.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Carrier inductive should register");
}

/// Register a "preorder-like" structure that `extends Carrier` with one extra
/// field, modelling Lean's `Preorder extends LE, LT …`:
///
/// `Pre.mk : (α : Type) → (toC : Carrier α) → (extra : α → α → α) → Pre α`
///
/// `Pre.mk` here has TWO real fields after the parameter. The WS15 import bug is
/// equivalent to registering it with only ONE field and then trying to apply
/// the (missing) second — which the kernel rejects. We register it CORRECTLY so
/// the projection chain reduces, then separately show the saturated-form
/// rejection.
fn add_pre(env: &mut Environment) {
    let pre = Name::from_string("Pre");
    let carrier = Name::from_string("Carrier");
    // Pre : Type → Type
    let pre_type = Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_());
    // toC : Carrier α   (under α binder)
    let to_c_ty = Expr::app(Expr::const_(carrier, vec![]), Expr::bvar(0));
    // extra : α → α → α (under α, toC binders)
    let extra_ty = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(1),
        Expr::pi(BinderInfo::Default, Expr::bvar(2), Expr::bvar(3)),
    );
    // Pre α   (under α, toC, extra binders)
    let pre_app = Expr::app(Expr::const_(pre.clone(), vec![]), Expr::bvar(2));
    // Pre.mk : (α : Type) → (toC : Carrier α) → (extra : α → α → α) → Pre α
    let mk_ty = Expr::pi(
        BinderInfo::Default,
        Expr::type_(),
        Expr::pi(
            BinderInfo::Default,
            to_c_ty,
            Expr::pi(BinderInfo::Default, extra_ty, pre_app),
        ),
    );
    env.add_inductive(InductiveDecl {
        level_params: vec![],
        num_params: 1,
        types: vec![InductiveType {
            name: pre,
            type_: pre_type,
            constructors: vec![Constructor {
                name: Name::from_string("Pre.mk"),
                type_: mk_ty,
            }],
        }],
    })
    .expect("Pre inductive should register");
}

/// `Carrier.mk Nat op` saturated has type `Carrier Nat`; applying it to a
/// further argument is `NotAFunction`. This is the EXACT shape the WS15
/// diagnostic observed for `Preorder.mk … le_trans` applied to the dropped
/// fifth field — the kernel correctly refuses to over-apply a saturated
/// constructor. (Soundness boundary; the real fix is import-side field count.)
#[test]
fn test_ws15_saturated_ctor_overapplication_is_not_a_function() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    add_carrier(&mut env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // op : Nat → Nat → Nat  ≡ Nat.add stand-in (use a fvar of the right type)
    let op_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );
    let tc = TypeChecker::new(&env);
    let op_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("op"), op_ty, BinderInfo::Default);
    let op = Expr::fvar(op_id);

    // Carrier.mk Nat op : Carrier Nat  (saturated)
    let saturated = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Carrier.mk"), vec![]),
            nat.clone(),
        ),
        op.clone(),
    );
    let saturated_ty = tc
        .infer_type(&saturated)
        .expect("saturated Carrier.mk should type-check");
    // Its type is `Carrier Nat`, NOT a function type.
    let carrier_nat = Expr::app(
        Expr::const_(Name::from_string("Carrier"), vec![]),
        nat.clone(),
    );
    assert!(
        tc.is_def_eq(&saturated_ty, &carrier_nat),
        "Carrier.mk Nat op : Carrier Nat"
    );

    // Over-applying the saturated constructor to a further argument is the WS15
    // shape: the kernel MUST reject it as NotAFunction (it is genuinely not a
    // function). The fix for the real failure is to give the imported
    // constructor its full field count — not to relax this check.
    let over_applied = Expr::app(saturated, op);
    let result = tc.infer_type(&over_applied);
    assert!(
        matches!(result, Err(crate::TypeError::NotAFunction { .. })),
        "over-applied saturated constructor must be NotAFunction, got {result:?}"
    );
}

/// SOUNDNESS PIN: a one-field structure *type* `Carrier α` must NEVER compare
/// definitionally equal to its sole field's type `α → α → α`. Equating them (a
/// tempting but unsound "fix" for the WS15 `Pi vs Mul` mismatches) would let a
/// value of a structure type be applied as a function. The kernel must reject.
#[test]
fn test_ws15_structure_type_not_defeq_to_field_type() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    add_carrier(&mut env);

    let env_ref = &env;
    let tc = TypeChecker::new(env_ref);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Carrier Nat  (a structure Type)
    let carrier_nat = Expr::app(
        Expr::const_(Name::from_string("Carrier"), vec![]),
        nat.clone(),
    );
    // Nat → Nat → Nat  (the field type)
    let fn_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );

    assert!(
        !tc.is_def_eq(&carrier_nat, &fn_ty),
        "SOUNDNESS: Carrier Nat (a structure type) must NOT be def-eq to Nat → Nat → Nat"
    );
    assert!(
        !tc.is_def_eq(&fn_ty, &carrier_nat),
        "SOUNDNESS (symmetric): Nat → Nat → Nat must NOT be def-eq to Carrier Nat"
    );
}

/// When a parent-`extends` structure is registered with its FULL field set, the
/// parent projection reduces through the constructor correctly — i.e. the
/// kernel is NOT the gap. `Pre.toC (Pre.mk α toC extra)` must reduce to `toC`
/// (here exercised via the field-0 projection inside a fully-applied
/// constructor), and the structure-eta / def-eq machinery confirms it.
#[test]
fn test_ws15_parent_projection_reduces_when_fully_registered() {
    let mut env = Environment::new();
    env.init_nat().expect("init_nat");
    add_carrier(&mut env);
    add_pre(&mut env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let op_ty = Expr::pi(
        BinderInfo::Default,
        nat.clone(),
        Expr::pi(BinderInfo::Default, nat.clone(), nat.clone()),
    );
    let tc = TypeChecker::new(&env);
    let op_id =
        tc.ctx
            .borrow_mut()
            .push(Name::from_string("op"), op_ty.clone(), BinderInfo::Default);
    let op = Expr::fvar(op_id);
    let extra_id = tc
        .ctx
        .borrow_mut()
        .push(Name::from_string("extra"), op_ty, BinderInfo::Default);
    let extra = Expr::fvar(extra_id);

    // toC := Carrier.mk Nat op : Carrier Nat
    let to_c = Expr::app(
        Expr::app(
            Expr::const_(Name::from_string("Carrier.mk"), vec![]),
            nat.clone(),
        ),
        op,
    );
    // Pre.mk Nat toC extra : Pre Nat   (FULLY applied — all declared fields present)
    let pre_val = Expr::app(
        Expr::app(
            Expr::app(
                Expr::const_(Name::from_string("Pre.mk"), vec![]),
                nat.clone(),
            ),
            to_c.clone(),
        ),
        extra,
    );
    // It type-checks (the constructor is saturated and well-typed).
    let pre_ty = tc
        .infer_type(&pre_val)
        .expect("fully-applied Pre.mk should type-check");
    let pre_nat = Expr::app(Expr::const_(Name::from_string("Pre"), vec![]), nat.clone());
    assert!(tc.is_def_eq(&pre_ty, &pre_nat), "Pre.mk … : Pre Nat");

    // Projecting field 0 (the `toC` parent) of the constructor application
    // reduces (iota/proj) back to `toC`.
    let proj0 = Expr::proj(Name::from_string("Pre"), 0, pre_val);
    assert!(
        tc.is_def_eq(&proj0, &to_c),
        "Pre field-0 projection of a constructor reduces to the toC parent — \
         the kernel reduces parent projections of fully-registered structures"
    );
}
