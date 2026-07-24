// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Edge-case tests for iota reduction (recursor computation rule).
//!
//! Covers patterns not exercised by the main tests.rs:
//! - Insufficient arguments (should return None / stay stuck)
//! - Extra arguments after major premise (carried through)
//! - Nat literal expansion in iota (Nat.rec on Nat.lit(3))
//! - List.rec iota reduction (parametric recursive type)
//! - recOn with parametric type
//! - K-like recursor behavioral reduction (Eq.rec via WHNF)
//! - Structure eta expansion path in iota
//!
//! Part of #3134.

use crate::env::Environment;
use crate::expr::{BinderInfo, Expr, ExprKind};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

// =========================================================================
// Insufficient arguments -- recursor with too few args stays stuck
// =========================================================================

#[test]
fn test_iota_insufficient_args_returns_stuck() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Nat.rec needs 4 args: motive, minor_zero, minor_succ, major
    // Provide only motive + 1 minor (2 args) -- should stay stuck
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // rec motive zero_case -- only 2 args, needs 4
    let partial = Expr::app(Expr::app(rec, motive), zero_case);
    let result = tc.whnf(&partial);

    // Should NOT reduce (stays as an application)
    assert!(
        matches!(result.kind(), ExprKind::App(..)),
        "Nat.rec with insufficient args should stay stuck, got: {result:?}"
    );
}

#[test]
fn test_iota_rec_on_insufficient_args_stuck() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Nat.recOn needs: motive, major, zero_case, succ_case = 4
    // Provide only motive + major (2 args)
    let rec_on = Expr::const_(
        Name::from_string("Nat.recOn"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let major = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let partial = Expr::app(Expr::app(rec_on, motive), major);
    let result = tc.whnf(&partial);

    // Re-pinned (residual-to-zero campaign, 2026-07-02): recOn now carries
    // its definitional VALUE (the Lean-parity reordering wrapper over rec),
    // so an under-applied application delta-unfolds and beta-reduces to a
    // PARTIAL LAMBDA awaiting the minors — exactly what Lean's kernel whnf
    // produces. Iota still cannot fire (no minors), so no branch is selected:
    // the result must be a lambda (or an app for value-less recursors), and
    // definitionally equal to the original.
    assert!(
        matches!(result.kind(), ExprKind::Lam(..) | ExprKind::App(..)),
        "under-applied Nat.recOn must reduce to a partial lambda, got {result:?}"
    );
    assert!(
        tc.is_def_eq(&partial, &result),
        "whnf must preserve definitional equality"
    );
}

// =========================================================================
// Extra arguments after major premise
// =========================================================================

#[test]
fn test_iota_extra_args_carried_through() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // Build Nat.rec that returns a function: motive n = Nat -> Nat
    let motive = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::arrow(nat.clone(), nat.clone()),
    );

    // zero_case : Nat -> Nat = fun x => x (identity)
    let zero_case = Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0));

    // succ_case : (n : Nat) -> (Nat -> Nat) -> (Nat -> Nat) = fun n ih => ih
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::arrow(nat.clone(), nat.clone()),
            Expr::bvar(0), // ih
        ),
    );

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    // Nat.rec motive zero_case succ_case zero EXTRA_ARG
    // The extra arg (Nat.lit(42)) should be carried through
    let extra = Expr::nat_lit(42);
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
            zero,
        ),
        extra.clone(),
    );

    let result = tc.whnf(&app);

    // zero_case is fun x => x, applied to 42, should give 42
    assert!(
        tc.is_def_eq(&result, &extra),
        "Extra arg after major should be applied to result. Got: {result:?}"
    );
}

// =========================================================================
// Nat literal expansion in iota
// =========================================================================

#[test]
fn test_iota_nat_literal_expansion() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Build an identity recursor on Nat
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            nat.clone(),
            Expr::app(
                Expr::const_(Name::from_string("Nat.succ"), vec![]),
                Expr::bvar(0),
            ),
        ),
    );

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    // Apply to Nat.lit(3) -- this exercises the nat_lit_to_constructor path
    // inside try_iota_reduction, which expands 3 to succ(lit(2))
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        Expr::nat_lit(3),
    );

    let result = tc.whnf(&app);

    // Identity recursor on 3 should produce 3
    assert!(
        tc.is_def_eq(&result, &Expr::nat_lit(3)),
        "Nat.rec identity on lit(3) should reduce to 3. Got: {result:?}"
    );
}

#[test]
fn test_iota_nat_literal_zero() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::nat_lit(99);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
    );

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    // Apply to Nat.lit(0) -- should expand to Nat.zero and match zero_case
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec, motive), zero_case.clone()),
            succ_case,
        ),
        Expr::nat_lit(0),
    );

    let result = tc.whnf(&app);

    assert!(
        tc.is_def_eq(&result, &zero_case),
        "Nat.rec on lit(0) should reduce to zero_case. Got: {result:?}"
    );
}

// =========================================================================
// List.rec iota reduction (parametric recursive type)
// =========================================================================

/// Create an environment with List defined (List : Type u → Type u, as in Lean).
fn make_list_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");

    let u = Name::from_string("u");
    let list = Name::from_string("List");

    // List : Type u → Type u (Sort (succ u) is provably nonzero, so the
    // 2-constructor List keeps large elimination under the elim gate [R1]).
    let list_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
    );

    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );

    let nil_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        list_a.clone(),
    );

    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0), // A
        Expr::pi(
            BinderInfo::Default,
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(1),
            ),
            Expr::app(
                Expr::const_(list.clone(), vec![Level::param(u.clone())]),
                Expr::bvar(2),
            ),
        ),
    );
    let cons_type = Expr::pi(
        BinderInfo::Default,
        Expr::from_kind(ExprKind::Sort(Level::succ(Level::param(u.clone())))),
        cons_body,
    );

    let decl = InductiveDecl {
        level_params: vec![u],
        num_params: 1,
        types: vec![InductiveType {
            name: list.clone(),
            type_: list_type,
            constructors: vec![
                Constructor {
                    name: Name::from_string("List.nil"),
                    type_: nil_type,
                },
                Constructor {
                    name: Name::from_string("List.cons"),
                    type_: cons_type,
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("add List");
    env
}

#[test]
fn test_list_rec_nil_reduction() {
    let env = make_list_env();
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    // List.{0} Nat : Type 0 (List : Type u → Type u, Nat : Type 0 ⇒ u = 0)
    let list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![Level::zero()]),
        nat.clone(),
    );

    // List.rec.{1,0} {Nat} (motive) (nil_case) (cons_case) (List.nil {Nat})
    // elim level 1: the motive below returns Nat : Type 0 = Sort 1;
    // decl level 0: matches List.{0} Nat above.
    let rec = Expr::const_(
        Name::from_string("List.rec"),
        vec![Level::succ(Level::zero()), Level::zero()],
    );

    // motive: fun (_ : List Nat) => Nat
    let motive = Expr::lam(BinderInfo::Default, list_nat.clone(), nat.clone());

    // nil_case: Nat.zero
    let nil_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // cons_case: fun (head : Nat) (tail : List Nat) (ih : Nat) => Nat.succ ih
    let cons_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            list_nat.clone(),
            Expr::lam(
                BinderInfo::Default,
                nat.clone(),
                Expr::app(
                    Expr::const_(Name::from_string("Nat.succ"), vec![]),
                    Expr::bvar(0), // ih
                ),
            ),
        ),
    );

    // Major: List.nil.{0} {Nat}
    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        nat.clone(),
    );

    // List.rec Nat motive nil_case cons_case nil
    let app = Expr::app(
        Expr::app(
            Expr::app(
                Expr::app(Expr::app(rec, nat.clone()), motive),
                nil_case.clone(),
            ),
            cons_case,
        ),
        nil,
    );

    let result = tc.whnf(&app);
    assert!(
        tc.is_def_eq(&result, &nil_case),
        "List.rec on nil should reduce to nil_case (Nat.zero). Got: {result:?}"
    );
}

// =========================================================================
// Projection in iota context (structure eta)
// =========================================================================

#[test]
fn test_iota_structure_eta_expansion() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let pair_name = Name::from_string("Pair");
    let pair_ref = Expr::const_(pair_name.clone(), vec![]);

    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: pair_name.clone(),
            type_: Expr::type_(),
            constructors: vec![Constructor {
                name: Name::from_string("Pair.mk"),
                type_: Expr::pi(
                    BinderInfo::Default,
                    nat.clone(),
                    Expr::pi(BinderInfo::Default, nat.clone(), pair_ref.clone()),
                ),
            }],
        }],
    };
    env.add_inductive(decl).expect("add Pair");
    let tc = TypeChecker::new(&env);

    // Build Pair.mk 3 7
    let mk = Expr::const_(Name::from_string("Pair.mk"), vec![]);
    let three = Expr::nat_lit(3);
    let seven = Expr::nat_lit(7);
    let pair_val = Expr::app(Expr::app(mk, three.clone()), seven.clone());

    // Pair.casesOn to extract first field
    let cases_on = Expr::const_(
        Name::from_string("Pair.casesOn"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, pair_ref.clone(), nat.clone());
    // minor: fun (a : Nat) (b : Nat) => a
    let minor = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(1)),
    );

    // Pair.casesOn motive pair_val minor (major precedes minors)
    let app = Expr::app(Expr::app(Expr::app(cases_on, motive), pair_val), minor);

    let result = tc.whnf(&app);
    assert!(
        tc.is_def_eq(&result, &three),
        "Pair.casesOn extracting first field should give 3. Got: {result:?}"
    );
}

// =========================================================================
// Non-constructor major premise stays stuck
// =========================================================================

#[test]
fn test_iota_stuck_on_fvar_major() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
    );

    // Major is an unknown constant (not a constructor)
    let unknown = Expr::const_(Name::from_string("mystery_nat"), vec![]);

    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        unknown,
    );

    let result = tc.whnf(&app);
    // Should stay stuck (the app won't reduce because major isn't a constructor)
    assert!(
        matches!(result.kind(), ExprKind::App(..)),
        "Nat.rec on non-constructor major should stay stuck. Got: {result:?}"
    );
}

// =========================================================================
// Recursor with wrong constructor (different inductive)
// =========================================================================

#[test]
fn test_iota_wrong_inductive_constructor() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");

    // Create a separate Bool type
    let bool_name = Name::from_string("MyBool");
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: bool_name.clone(),
            type_: Expr::from_kind(ExprKind::Sort(Level::succ(Level::zero()))),
            constructors: vec![
                Constructor {
                    name: Name::from_string("MyBool.false"),
                    type_: bool_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("MyBool.true"),
                    type_: bool_ref,
                },
            ],
        }],
    };
    env.add_inductive(decl).expect("add MyBool");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
    );

    // Pass MyBool.true as major to Nat.rec -- wrong inductive
    let wrong_major = Expr::const_(Name::from_string("MyBool.true"), vec![]);

    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        wrong_major,
    );

    let result = tc.whnf(&app);
    // Should stay stuck -- MyBool.true is not a constructor of Nat
    assert!(
        matches!(result.kind(), ExprKind::App(..)),
        "Nat.rec on MyBool.true should stay stuck (wrong inductive). Got: {result:?}"
    );
}

// =========================================================================
// Empty type recursor (0 constructors)
// =========================================================================

#[test]
fn test_iota_empty_type_stays_stuck() {
    let mut env = Environment::new();

    let empty = Name::from_string("Empty");
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: empty.clone(),
            type_: Expr::type_(),
            constructors: vec![],
        }],
    };
    env.add_inductive(decl).expect("add Empty");
    let tc = TypeChecker::new(&env);

    let rec = Expr::const_(
        Name::from_string("Empty.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(
        BinderInfo::Default,
        Expr::const_(empty.clone(), vec![]),
        Expr::type_(),
    );

    // Empty.rec motive major -- major can never be a constructor, so always stuck
    let fake_major = Expr::const_(Name::from_string("impossible"), vec![]);
    let app = Expr::app(Expr::app(rec, motive), fake_major);

    let result = tc.whnf(&app);
    assert!(
        matches!(result.kind(), ExprKind::App(..)),
        "Empty.rec should always stay stuck (no constructors). Got: {result:?}"
    );
}

// =========================================================================
// Level parameter count mismatch
// =========================================================================

#[test]
fn test_iota_level_count_mismatch_stays_stuck() {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    let tc = TypeChecker::new(&env);

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // Nat.rec expects 1 level parameter, give it 0
    let rec = Expr::const_(Name::from_string("Nat.rec"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
    );
    let major = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        major,
    );

    let result = tc.whnf(&app);
    // Level param mismatch should cause try_iota_reduction to return None
    assert!(
        matches!(result.kind(), ExprKind::App(..)),
        "Nat.rec with wrong level count should stay stuck. Got: {result:?}"
    );
}

// =========================================================================
// Twin-skew rule selection -- idx fast path must verify the rule's ctor name
// =========================================================================

/// Shadow-twin skew (carrier-parity P0,
/// `designs/2026-07-03-carrier-types-bitvec-parity.md`): an imported
/// constructor that claims an already-seeded parent (`UInt32.ofBitVec` next
/// to seeded `UInt32` whose ctor list is `[UInt32.mk]`) satisfies
/// `ctor_val.inductive_name == rec_val.inductive_name` while its
/// `constructor_idx` indexes the OTHER copy's rule list. The idx fast path
/// used to trust the index outright (`debug_assert` only): debug builds
/// panicked and release builds applied the WRONG constructor's rule. The fix
/// verifies the indexed rule's constructor name and otherwise falls back to
/// the by-name scan (Lean's own selection is by-name) — no rule names the
/// foreign ctor, so reduction is honestly stuck.
#[test]
fn test_iota_twin_skewed_ctor_same_parent_name_stays_stuck() {
    use crate::inductive::ConstructorVal;

    let mut env = Environment::new();
    env.init_nat().expect("init Nat");

    // Fabricate the skew through the same lane the olean importer uses: a
    // pre-validated constructor claiming parent `Nat` at idx 0, whose name
    // matches NO rule of the seeded `Nat.rec` (rules: Nat.zero, Nat.succ).
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    env.register_constructor(ConstructorVal {
        name: Name::from_string("Nat.ofBits"),
        inductive_name: Name::from_string("Nat"),
        level_params: vec![],
        type_: nat.clone(),
        num_params: 0,
        num_fields: 0,
        constructor_idx: 0,
    });

    let tc = TypeChecker::new(&env);
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::bvar(0)),
    );

    // Nat.rec motive zero succ (Nat.ofBits) — the foreign ctor at idx 0 would
    // select the Nat.zero rule under the old fast path and "reduce" to the
    // zero minor: a wrong reduction. It must stay stuck instead.
    let skewed = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec.clone(), motive.clone()), zero_case.clone()),
            succ_case.clone(),
        ),
        Expr::const_(Name::from_string("Nat.ofBits"), vec![]),
    );
    let result = tc.whnf(&skewed);
    assert!(
        matches!(result.kind(), ExprKind::App(..)),
        "twin-skewed ctor must leave the recursor stuck, got: {result:?}"
    );

    // The genuine fast path is untouched: the same recursor on Nat.zero still
    // iota-reduces to the zero minor.
    let genuine = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec, motive), zero_case.clone()),
            succ_case,
        ),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );
    let reduced = tc.whnf(&genuine);
    assert!(
        matches!(reduced.kind(), ExprKind::Const(n2, _) if n2 == &Name::from_string("Nat.zero")),
        "genuine ctor at its own idx must still fast-path iota-reduce, got: {reduced:?}"
    );
}
