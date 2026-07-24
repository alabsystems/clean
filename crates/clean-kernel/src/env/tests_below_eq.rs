// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for `.brecOn.go`, `.brecOn.eq` equation lemma patterns.
//!
//! In Lean 4, `.brecOn` is split into three parts:
//! 1. `T.brecOn.go` — returns `PProd (motive t) (T.below t)` via the recursor
//! 2. `T.brecOn` — projects first component: `(T.brecOn.go ...).1`
//! 3. `T.brecOn.eq` — equation lemma: `brecOn t F = F t (brecOn.go ...).2`
//!
//! The equation lemma's proof is `casesOn t (fun ... => Eq.refl ...)`, which
//! requires the TC to reduce `brecOn` applications through delta + iota.
//!
//! This test suite verifies that clean's TC can handle these patterns,
//! reproducing the `Lean.Syntax.brecOn_2.eq` TypeMismatch failure (#3134).

use super::test_helpers::assert_const;
use super::*;
use crate::env::types::{ConstantInfo, Declaration, Reducibility};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::tc::TypeChecker;

/// Create an environment with Nat, PUnit, PProd, Eq, and the Nat.below/brecOn definitions.
fn make_nat_brec_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_punit().unwrap();
    env.init_pprod().unwrap();

    let nat = Name::from_string("Nat");
    let nat_ref = Expr::const_(nat.clone(), vec![]);
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 0,
        types: vec![InductiveType {
            name: nat.clone(),
            type_: Expr::type_(),
            constructors: vec![
                Constructor {
                    name: Name::from_string("Nat.zero"),
                    type_: nat_ref.clone(),
                },
                Constructor {
                    name: Name::from_string("Nat.succ"),
                    type_: Expr::arrow(nat_ref.clone(), nat_ref),
                },
            ],
        }],
    };
    env.add_inductive(decl).unwrap();
    env
}

/// Test: Nat.brecOn value is well-typed (basic sanity check).
#[test]
fn test_nat_brec_on_value_well_typed() {
    let env = make_nat_brec_env();
    let ci = env
        .get_const(&Name::from_string("Nat.brecOn"))
        .expect("Nat.brecOn should exist");
    let value = ci.value.as_ref().expect("should have value");
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("Nat.brecOn value should type-check");
}

/// Test: Nat.below value is well-typed.
#[test]
fn test_nat_below_value_well_typed() {
    let env = make_nat_brec_env();
    let ci = env
        .get_const(&Name::from_string("Nat.below"))
        .expect("Nat.below should exist");
    let value = ci.value.as_ref().expect("should have value");
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("Nat.below value should type-check");
}

/// Test: manually construct `Nat.brecOn.go` (Lean 4 style) and verify it type-checks.
///
/// `Nat.brecOn.go` returns the full `PProd (motive t) (Nat.below t)` pair
/// rather than projecting. This is how Lean 4 generates brecOn:
///
/// ```
/// def Nat.brecOn.go {motive : Nat → Sort u} (t : Nat)
///     (F : (t : Nat) → Nat.below t → motive t) : PProd (motive t) (Nat.below t) :=
///   Nat.rec ⟨F 0 PUnit.unit, PUnit.unit⟩
///           (fun n ih => ⟨F (n+1) ih, ih⟩) t
/// ```
#[test]
fn test_nat_brec_on_go_construction() {
    let env = make_nat_brec_env();

    // Get the existing brecOn to understand the structure
    let brec_ci = env
        .get_const(&Name::from_string("Nat.brecOn"))
        .expect("Nat.brecOn should exist");
    let brec_value = brec_ci.value.as_ref().unwrap();

    // The brecOn value should contain PProd.fst (Proj(PProd, 0, ...))
    // The .go version is the same but without the projection.
    // We verify this by checking that brecOn's value contains a Proj node.
    fn has_proj(e: &Expr) -> bool {
        match &e.kind {
            ExprKind::Proj(..) => true,
            ExprKind::App(f, a) => has_proj(f) || has_proj(a),
            ExprKind::Lam(_, t, b) => has_proj(t) || has_proj(b),
            ExprKind::Pi(_, t, b) => has_proj(t) || has_proj(b),
            _ => false,
        }
    }
    assert!(
        has_proj(brec_value),
        "Nat.brecOn value should contain a Proj (PProd.fst)"
    );
}

/// Test: applying Nat.brecOn to Nat.zero reduces correctly via WHNF.
///
/// `Nat.brecOn @motive Nat.zero F` should reduce to `F Nat.zero PUnit.unit`
/// because:
/// 1. brecOn unfolds to `Proj(PProd, 0, Nat.rec ...)`
/// 2. Nat.rec motive (zero_minor) (succ_minor) Nat.zero → iota → zero_minor
/// 3. zero_minor = `PProd.mk (F 0 PUnit.unit) PUnit.unit`
/// 4. Proj(PProd, 0, PProd.mk a b) → a = `F 0 PUnit.unit`
#[test]
fn test_nat_brec_on_zero_reduces() {
    let env = make_nat_brec_env();
    let u = Name::from_string("u");

    // Build: @Nat.brecOn.{u} @motive Nat.zero F
    // where motive : Nat → Sort u, F : (t : Nat) → Nat.below t → motive t
    // We test with motive = fun _ => Nat (i.e., u = 1)

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone()); // fun _ : Nat => Nat

    // F : (t : Nat) → Nat.below @motive t → Nat
    // Use a simple F: fun t below_t => t
    let below_app = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("Nat.below"),
                vec![Level::succ(Level::zero())],
            ),
            motive.clone(),
        ),
        Expr::bvar(0),
    );
    let f_body = Expr::bvar(1); // return the first arg (t)
    let f = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, below_app, f_body),
    );

    let brec_app = Expr::apps(
        Expr::const_(
            Name::from_string("Nat.brecOn"),
            vec![Level::succ(Level::zero())],
        ),
        [
            motive,
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
            f,
        ],
    );

    let tc = TypeChecker::new(&env);
    let result = tc.whnf(&brec_app);

    // The result should reduce. If brecOn is working correctly,
    // it should reduce to F(Nat.zero, PUnit.unit) which is Nat.zero.
    // At minimum, the WHNF should not be stuck at the brecOn application.
    assert!(
        !matches!(result.get_app_fn().kind(), ExprKind::Const(n, _) if n == &Name::from_string("Nat.brecOn")),
        "Nat.brecOn application on Nat.zero should reduce (not stay stuck at brecOn head)"
    );
}

/// Test: brecOn.eq style equation lemma for Nat (zero case).
///
/// The equation lemma states:
///   `Nat.brecOn t F = F t (Nat.brecOn.go t F).2`
///
/// For the zero case, both sides should reduce to the same thing by `refl`.
/// This tests the key pattern that fails for `Lean.Syntax.brecOn_2.eq`.
#[test]
fn test_nat_brec_on_eq_refl_zero_case() {
    let env = make_nat_brec_env();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u_level = Level::succ(Level::zero()); // Sort 1 = Type 0

    // motive: fun _ : Nat => Nat
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());

    // below motive : Nat → Sort (max 1 1) = Nat → Sort 1
    let below_app_fn = Expr::app(
        Expr::const_(Name::from_string("Nat.below"), vec![u_level.clone()]),
        motive.clone(),
    );

    // f_type: (t : Nat) → Nat.below @motive t → Nat
    // F: fun t below_t => t
    let f_body = Expr::bvar(1); // return t
    let f = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(below_app_fn.clone(), Expr::bvar(0)),
            f_body,
        ),
    );

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // LHS: Nat.brecOn @motive Nat.zero F
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Nat.brecOn"), vec![u_level.clone()]),
        [motive.clone(), zero.clone(), f.clone()],
    );

    // Reduce LHS
    let tc = TypeChecker::new(&env);
    let lhs_whnf = tc.whnf(&lhs);

    // The LHS should reduce to F(Nat.zero, PUnit.unit) = Nat.zero
    // (since F = fun t _ => t and t = Nat.zero)

    // RHS: F Nat.zero (something).2
    // For the zero case, the "something" is the full rec result which for zero
    // is PProd.mk (F 0 PUnit.unit) PUnit.unit. So .2 = PUnit.unit.
    let rhs = Expr::app(Expr::app(f.clone(), zero.clone()), {
        // PUnit.unit at level (max 1 u) = PUnit.unit at level 1
        let rlvl = Level::max(Level::zero(), u_level.clone());
        Expr::const_(Name::from_string("PUnit.unit"), vec![rlvl])
    });
    let rhs_whnf = tc.whnf(&rhs);

    // Both sides should be definitionally equal
    assert!(
        tc.is_def_eq(&lhs_whnf, &rhs_whnf),
        "LHS and RHS of brecOn.eq (zero case) should be definitionally equal.\n\
         LHS WHNF: {lhs_whnf:?}\n\
         RHS WHNF: {rhs_whnf:?}"
    );
}

/// Construct a `Nat.brecOn.go` definition in Lean 4's style and add it to the env.
///
/// `Nat.brecOn.go` is the same as clean's `Nat.brecOn` but WITHOUT the final
/// PProd.fst projection. It returns the full `PProd (motive t) (Nat.below t)`.
///
/// Lean 4 definition:
/// ```
/// def Nat.brecOn.go {motive : Nat → Sort u} (t : Nat)
///     (F : (t : Nat) → Nat.below t → motive t)
///     : PProd (motive t) (Nat.below t) :=
///   Nat.rec ⟨F 0 PUnit.unit, PUnit.unit⟩
///           (fun n ih => ⟨F (n+1) ih, ih⟩) t
/// ```
fn add_nat_brec_on_go(env: &mut Environment) {
    let brec_ci = env
        .get_const(&Name::from_string("Nat.brecOn"))
        .expect("Nat.brecOn should exist");
    let brec_value = brec_ci.value.as_ref().unwrap().clone();
    let brec_levels = brec_ci.level_params.clone();

    // The brecOn value is: fun {motive} t F => Proj(PProd, 0, rec_app)
    // We need to remove the Proj to get the .go value.
    // Also, the .go type returns PProd(motive t)(below t) instead of motive t.
    fn strip_outer_proj(e: &Expr) -> Expr {
        match &e.kind {
            ExprKind::Lam(bi, ty, body) => Expr::from_kind(ExprKind::Lam(
                *bi,
                ty.clone(),
                strip_outer_proj(body).into(),
            )),
            ExprKind::Proj(_name, _idx, inner) => (**inner).clone(),
            _ => e.clone(),
        }
    }

    let go_value = strip_outer_proj(&brec_value);

    // For the type, we need to change the return type from `motive t` to
    // `PProd (motive t) (Nat.below motive t)`.
    // Infer the type from the value using a temporary TypeChecker scope.
    let go_type = {
        let tc = TypeChecker::new(env);
        tc.infer_type(&go_value)
            .expect("go value should type-check")
    };

    let mut go_info = ConstantInfo::new(
        Name::from_string("Nat.brecOn.go"),
        brec_levels,
        go_type,
        Some(go_value),
        true,
    );
    go_info.reducibility = Reducibility::Reducible;
    env.extend_constants_unchecked(std::iter::once(go_info));
}

/// Test: Nat.brecOn.go construction and type-checking.
#[test]
fn test_nat_brec_on_go_type_checks() {
    let mut env = make_nat_brec_env();
    add_nat_brec_on_go(&mut env);

    let ci = env
        .get_const(&Name::from_string("Nat.brecOn.go"))
        .expect("Nat.brecOn.go should exist");
    let value = ci.value.as_ref().expect("should have value");
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("Nat.brecOn.go value should type-check");
}

/// Test: Nat.brecOn.eq equation lemma pattern type-checks.
///
/// The equation lemma states (for the zero case):
///   `@Nat.brecOn.{u} @motive Nat.zero F = F Nat.zero (Nat.brecOn.go @motive Nat.zero F).2`
///
/// This tests both sides of the equation reduce to the same value.
#[test]
fn test_nat_brec_on_eq_via_go() {
    let mut env = make_nat_brec_env();
    add_nat_brec_on_go(&mut env);

    let u_level = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    // motive: fun _ : Nat => Nat
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());

    // below motive : Nat → Sort (max 1 1)
    let below_app = Expr::app(
        Expr::const_(Name::from_string("Nat.below"), vec![u_level.clone()]),
        motive.clone(),
    );

    // F: fun t (_ : Nat.below motive t) => t (identity-like)
    let f = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(below_app.clone(), Expr::bvar(0)),
            Expr::bvar(1), // return t
        ),
    );

    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);

    // LHS: Nat.brecOn @motive Nat.zero F
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Nat.brecOn"), vec![u_level.clone()]),
        [motive.clone(), zero.clone(), f.clone()],
    );

    // RHS: F Nat.zero (Nat.brecOn.go @motive Nat.zero F).2
    let go_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.brecOn.go"), vec![u_level.clone()]),
        [motive.clone(), zero.clone(), f.clone()],
    );
    let go_snd = Expr::proj(Name::from_string("PProd"), 1, go_app);
    let rhs = Expr::app(Expr::app(f.clone(), zero.clone()), go_snd);

    let tc = TypeChecker::new(&env);

    // Verify LHS and RHS are definitionally equal
    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "brecOn.eq: LHS and RHS should be definitionally equal for zero case.\n\
         LHS: {lhs:?}\n\
         RHS: {rhs:?}\n\
         LHS WHNF: {:?}\n\
         RHS WHNF: {:?}",
        tc.whnf(&lhs),
        tc.whnf(&rhs),
    );
}

/// Test: Nat.brecOn.eq equation lemma for the succ case.
///
/// For Nat.succ n, the equation should also hold:
///   `@Nat.brecOn @motive (Nat.succ n) F = F (Nat.succ n) (Nat.brecOn.go @motive (Nat.succ n) F).2`
#[test]
fn test_nat_brec_on_eq_via_go_succ() {
    let mut env = make_nat_brec_env();
    add_nat_brec_on_go(&mut env);

    let u_level = Level::succ(Level::zero());
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);

    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let below_app = Expr::app(
        Expr::const_(Name::from_string("Nat.below"), vec![u_level.clone()]),
        motive.clone(),
    );
    let f = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(below_app.clone(), Expr::bvar(0)),
            Expr::bvar(1),
        ),
    );

    // Use Nat.succ(Nat.zero) as the major
    let one = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::const_(Name::from_string("Nat.zero"), vec![]),
    );

    // LHS: Nat.brecOn @motive (Nat.succ 0) F
    let lhs = Expr::apps(
        Expr::const_(Name::from_string("Nat.brecOn"), vec![u_level.clone()]),
        [motive.clone(), one.clone(), f.clone()],
    );

    // RHS: F (Nat.succ 0) (Nat.brecOn.go @motive (Nat.succ 0) F).2
    let go_app = Expr::apps(
        Expr::const_(Name::from_string("Nat.brecOn.go"), vec![u_level.clone()]),
        [motive.clone(), one.clone(), f.clone()],
    );
    let go_snd = Expr::proj(Name::from_string("PProd"), 1, go_app);
    let rhs = Expr::app(Expr::app(f.clone(), one.clone()), go_snd);

    let tc = TypeChecker::new(&env);

    assert!(
        tc.is_def_eq(&lhs, &rhs),
        "brecOn.eq: LHS and RHS should be definitionally equal for succ case.\n\
         LHS: {lhs:?}\n\
         RHS: {rhs:?}\n\
         LHS WHNF: {:?}\n\
         RHS WHNF: {:?}",
        tc.whnf(&lhs),
        tc.whnf(&rhs),
    );
}

/// Create an environment with List (parametric recursive), including below/brecOn.
fn make_list_brec_env() -> Environment {
    let mut env = Environment::new();
    env.init_eq().unwrap();
    env.init_punit().unwrap();
    env.init_pprod().unwrap();
    env.init_nat().unwrap();

    let u = Name::from_string("u");
    let list = Name::from_string("List");
    let u_succ = Level::succ(Level::param(u.clone()));
    let type_u = Expr::from_kind(ExprKind::Sort(u_succ.clone()));
    let list_type = Expr::pi(BinderInfo::Default, type_u.clone(), type_u.clone());
    let list_a = Expr::app(
        Expr::const_(list.clone(), vec![Level::param(u.clone())]),
        Expr::bvar(0),
    );
    let nil_type = Expr::pi(BinderInfo::Default, type_u.clone(), list_a.clone());
    let cons_body = Expr::pi(
        BinderInfo::Default,
        Expr::bvar(0),
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
    let cons_type = Expr::pi(BinderInfo::Default, type_u, cons_body);
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
    env.add_inductive(decl).unwrap();
    env
}

/// Test: List.brecOn is generated and type-checks.
#[test]
fn test_list_brec_on_value_type_checks_with_eq() {
    let env = make_list_brec_env();
    let ci = env
        .get_const(&Name::from_string("List.brecOn"))
        .expect("List.brecOn should exist");
    let value = ci.value.as_ref().expect("should have value");
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("List.brecOn value should type-check");
}

/// Test: List.below value type-checks.
#[test]
fn test_list_below_value_type_checks_with_eq() {
    let env = make_list_brec_env();
    let ci = env
        .get_const(&Name::from_string("List.below"))
        .expect("List.below should exist");
    let value = ci.value.as_ref().expect("should have value");
    let tc = TypeChecker::new(&env);
    tc.check_type(value, &ci.type_)
        .expect("List.below value should type-check");
}

/// Test: applying List.brecOn to List.nil reduces.
///
/// `List.brecOn @Nat @motive (List.nil @Nat) F` should reduce through
/// delta + iota, not get stuck.
#[test]
fn test_list_brec_on_nil_reduces() {
    let env = make_list_brec_env();

    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let u_level = Level::succ(Level::zero()); // u = 1
    let list_nat = Expr::app(
        Expr::const_(Name::from_string("List"), vec![u_level.clone()]),
        nat.clone(),
    );

    // motive: fun _ : List Nat => Nat
    let motive = Expr::lam(BinderInfo::Default, list_nat.clone(), nat.clone());

    let nil = Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![u_level.clone()]),
        nat.clone(),
    );

    // below_app = List.below @Nat @motive
    let below_app = Expr::app(
        Expr::app(
            Expr::const_(
                Name::from_string("List.below"),
                vec![Level::succ(Level::zero()), u_level.clone()],
            ),
            nat.clone(),
        ),
        motive.clone(),
    );

    // F: fun (t : List Nat) (b : List.below @Nat @motive t) => Nat.zero
    let f = Expr::lam(
        BinderInfo::Default,
        list_nat.clone(),
        Expr::lam(
            BinderInfo::Default,
            Expr::app(below_app.clone(), Expr::bvar(0)),
            Expr::const_(Name::from_string("Nat.zero"), vec![]),
        ),
    );

    let brec_app = Expr::apps(
        Expr::const_(
            Name::from_string("List.brecOn"),
            vec![Level::succ(Level::zero()), u_level],
        ),
        [nat, motive, nil, f],
    );

    let tc = TypeChecker::new(&env);
    let result = tc.whnf(&brec_app);

    // Should reduce (not stay stuck at List.brecOn head)
    let head_name = match result.get_app_fn().kind() {
        ExprKind::Const(n, _) => Some(n.to_string()),
        _ => None,
    };
    assert!(
        head_name.as_deref() != Some("List.brecOn"),
        "List.brecOn application on List.nil should reduce.\nResult: {result:?}"
    );
}
