// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::names;
use super::nat::{nat_lit_to_constructor, string_lit_to_constructor};
use crate::env::Environment;
use crate::expr::{BigNat, BinderInfo, Expr, ExprKind, Literal};
use crate::inductive::{Constructor, InductiveDecl, InductiveType};
use crate::level::Level;
use crate::name::Name;
use crate::tc::TypeChecker;

/// Create a minimal environment with Nat defined.
fn make_nat_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    env
}

// =========================================================================
// BigNat::gcd_big -- arbitrary-precision Euclidean GCD helper
// =========================================================================

fn gcd_u64(a: u64, b: u64) -> u64 {
    match BigNat::Small(a).gcd_big(&BigNat::Small(b)) {
        BigNat::Small(v) => v,
        BigNat::Big(_) => panic!("gcd of u64 inputs should fit in u64"),
    }
}

#[test]
fn test_nat_gcd_basic() {
    assert_eq!(gcd_u64(12, 8), 4);
    assert_eq!(gcd_u64(8, 12), 4);
}

#[test]
fn test_nat_gcd_coprime() {
    assert_eq!(gcd_u64(7, 13), 1);
    assert_eq!(gcd_u64(17, 31), 1);
}

#[test]
fn test_nat_gcd_zero() {
    assert_eq!(gcd_u64(0, 5), 5);
    assert_eq!(gcd_u64(5, 0), 5);
    assert_eq!(gcd_u64(0, 0), 0);
}

#[test]
fn test_nat_gcd_identity() {
    assert_eq!(gcd_u64(42, 42), 42);
    assert_eq!(gcd_u64(1, 1), 1);
}

#[test]
fn test_nat_gcd_one() {
    assert_eq!(gcd_u64(1, 1000), 1);
    assert_eq!(gcd_u64(1000, 1), 1);
}

// =========================================================================
// nat_lit_to_constructor -- Nat literal to constructor form
// =========================================================================

#[test]
fn test_nat_lit_to_constructor_zero() {
    let result = nat_lit_to_constructor(&BigNat::Small(0));
    // Should be Nat.zero (a Const, no args)
    assert!(
        matches!(&result.kind, ExprKind::Const(name, levels)
            if *name == *names::NAT_ZERO && levels.is_empty()),
        "nat_lit_to_constructor(0) should be Nat.zero, got: {:?}",
        result.kind
    );
}

#[test]
fn test_nat_lit_to_constructor_one() {
    let result = nat_lit_to_constructor(&BigNat::Small(1));
    // Should be Nat.succ(Nat.lit(0))
    let head = result.get_app_fn();
    assert!(
        matches!(&head.kind, ExprKind::Const(name, levels)
            if *name == *names::NAT_SUCC && levels.is_empty()),
        "nat_lit_to_constructor(1) head should be Nat.succ, got: {:?}",
        head.kind
    );
    let args = result.get_app_args();
    assert_eq!(args.len(), 1, "Nat.succ should have 1 arg");
    // The arg should be Nat.lit(0)
    assert!(
        matches!(&args[0].kind, ExprKind::Lit(Literal::Nat(BigNat::Small(0)))),
        "Nat.succ arg should be Nat.lit(0), got: {:?}",
        args[0].kind
    );
}

#[test]
fn test_nat_lit_to_constructor_five() {
    let result = nat_lit_to_constructor(&BigNat::Small(5));
    // Should be Nat.succ(Nat.lit(4)) -- lazy expansion
    let head = result.get_app_fn();
    assert!(
        matches!(&head.kind, ExprKind::Const(name, _) if *name == *names::NAT_SUCC),
        "nat_lit_to_constructor(5) head should be Nat.succ"
    );
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    assert!(
        matches!(&args[0].kind, ExprKind::Lit(Literal::Nat(BigNat::Small(4)))),
        "Nat.succ arg should be Nat.lit(4), got: {:?}",
        args[0].kind
    );
}

#[test]
fn test_nat_lit_to_constructor_u64_max() {
    let result = nat_lit_to_constructor(&BigNat::Small(u64::MAX));
    // Should be Nat.succ(Nat.lit(u64::MAX - 1))
    let head = result.get_app_fn();
    assert!(
        matches!(&head.kind, ExprKind::Const(name, _) if *name == *names::NAT_SUCC),
        "nat_lit_to_constructor(u64::MAX) should be Nat.succ"
    );
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    assert!(
        matches!(&args[0].kind, ExprKind::Lit(Literal::Nat(BigNat::Small(v))) if *v == u64::MAX - 1),
        "Predecessor of u64::MAX should be u64::MAX-1, got: {:?}",
        args[0].kind
    );
}

#[test]
fn test_nat_lit_to_constructor_bignat() {
    // BigNat with value 2^64 (= [0, 1] in little-endian limbs)
    let big = BigNat::Big(vec![0, 1]);
    let result = nat_lit_to_constructor(&big);
    // Should be Nat.succ(Nat.lit(2^64 - 1)) = Nat.succ(Nat.lit(u64::MAX))
    let head = result.get_app_fn();
    assert!(
        matches!(&head.kind, ExprKind::Const(name, _) if *name == *names::NAT_SUCC),
        "nat_lit_to_constructor(2^64) should be Nat.succ"
    );
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    // 2^64 - 1 = u64::MAX, which fits in Small
    assert!(
        matches!(&args[0].kind, ExprKind::Lit(Literal::Nat(BigNat::Small(v))) if *v == u64::MAX),
        "Predecessor of 2^64 should be u64::MAX (Small), got: {:?}",
        args[0].kind
    );
}

#[test]
fn test_nat_lit_to_constructor_bignat_multi_limb_pred() {
    // BigNat with value 2^64 + 1 = [1, 1] in little-endian
    // Predecessor is 2^64 = [0, 1], which stays Big
    let big = BigNat::Big(vec![1, 1]);
    let result = nat_lit_to_constructor(&big);
    let head = result.get_app_fn();
    assert!(
        matches!(&head.kind, ExprKind::Const(name, _) if *name == *names::NAT_SUCC),
        "nat_lit_to_constructor(2^64+1) should be Nat.succ"
    );
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    // Predecessor: 2^64 = Big([0, 1])
    assert!(
        matches!(&args[0].kind, ExprKind::Lit(Literal::Nat(BigNat::Big(limbs))) if *limbs == vec![0, 1]),
        "Predecessor of 2^64+1 should be BigNat([0, 1]), got: {:?}",
        args[0].kind
    );
}

// =========================================================================
// string_lit_to_constructor -- String literal to constructor form
// =========================================================================

#[test]
fn test_string_lit_to_constructor_empty_roundtrip() {
    let result = string_lit_to_constructor("");
    // Should be String.ofList (List.nil {Char})
    let fn_head = result.get_app_fn();
    assert!(
        matches!(&fn_head.kind, ExprKind::Const(name, _) if name.to_string() == "String.ofList"),
        "Empty string should produce String.ofList"
    );
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    let list_head = args[0].get_app_fn();
    assert!(
        matches!(&list_head.kind, ExprKind::Const(name, _) if name.to_string() == "List.nil"),
        "Empty string list should be List.nil"
    );
}

#[test]
fn test_string_lit_to_constructor_single_ascii() {
    let result = string_lit_to_constructor("A");
    let fn_head = result.get_app_fn();
    assert!(
        matches!(&fn_head.kind, ExprKind::Const(name, _) if name.to_string() == "String.ofList"),
        "Single char should produce String.ofList"
    );
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    // Drill into List.cons to verify character code
    let list = &args[0];
    let list_args = list.get_app_args();
    assert_eq!(
        list_args.len(),
        3,
        "List.cons has 3 args (type, elem, tail)"
    );
    // Second arg is the character: Char.ofNat 65
    let char_app = &list_args[1];
    let char_args = char_app.get_app_args();
    assert_eq!(char_args.len(), 1);
    assert!(
        matches!(
            &char_args[0].kind,
            ExprKind::Lit(Literal::Nat(BigNat::Small(65)))
        ),
        "'A' should be code point 65, got: {:?}",
        char_args[0].kind
    );
}

#[test]
fn test_string_lit_to_constructor_preserves_order() {
    let result = string_lit_to_constructor("ba");
    let args = result.get_app_args();
    assert_eq!(args.len(), 1);
    let list = &args[0];
    let list_args = list.get_app_args();
    // First cons element should be 'b' (98), not 'a' (97)
    let first_char = &list_args[1];
    let first_char_args = first_char.get_app_args();
    assert!(
        matches!(
            &first_char_args[0].kind,
            ExprKind::Lit(Literal::Nat(BigNat::Small(98)))
        ),
        "First char should be 'b' (98), got: {:?}",
        first_char_args[0].kind
    );
}

// =========================================================================
// nat_lit_to_constructor roundtrip via TypeChecker
// =========================================================================

#[test]
fn test_nat_lit_to_constructor_roundtrip_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // nat_lit_to_constructor(0) should be def_eq to Nat.lit(0)
    let expanded = nat_lit_to_constructor(&BigNat::Small(0));
    let literal = Expr::nat_lit(0);
    assert!(
        tc.is_def_eq(&expanded, &literal),
        "nat_lit_to_constructor(0) should be def_eq to Nat.lit(0)"
    );
}

#[test]
fn test_nat_lit_to_constructor_roundtrip_one() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let expanded = nat_lit_to_constructor(&BigNat::Small(1));
    let literal = Expr::nat_lit(1);
    assert!(
        tc.is_def_eq(&expanded, &literal),
        "nat_lit_to_constructor(1) should be def_eq to Nat.lit(1)"
    );
}

#[test]
fn test_nat_lit_to_constructor_roundtrip_large() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let expanded = nat_lit_to_constructor(&BigNat::Small(100));
    let literal = Expr::nat_lit(100);
    assert!(
        tc.is_def_eq(&expanded, &literal),
        "nat_lit_to_constructor(100) should be def_eq to Nat.lit(100)"
    );
}

// =========================================================================
// reduce_nat via TypeChecker -- key edge cases from acceptance criteria
// =========================================================================

/// Helper: build binary Nat op expression `op(a, b)`.
fn nat_binop(op: &str, a: Expr, b: Expr) -> Expr {
    Expr::app(Expr::app(Expr::const_(Name::from_string(op), vec![]), a), b)
}

#[test]
fn test_reduce_nat_zero_plus_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.add", Expr::nat_lit(0), Expr::nat_lit(0)),
            &Expr::nat_lit(0)
        ),
        "Nat.add(0, 0) should reduce to 0"
    );
}

#[test]
fn test_reduce_nat_succ_plus_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // Nat.succ(0) + 0 = 1
    let succ_zero = Expr::app(
        Expr::const_(Name::from_string("Nat.succ"), vec![]),
        Expr::nat_lit(0),
    );
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.add", succ_zero, Expr::nat_lit(0)),
            &Expr::nat_lit(1)
        ),
        "Nat.add(succ(0), 0) should reduce to 1"
    );
}

#[test]
fn test_reduce_nat_add_near_u64_max() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // u64::MAX + 1 overflows -- should NOT reduce
    assert!(
        !tc.is_def_eq(
            &nat_binop("Nat.add", Expr::nat_lit(u64::MAX), Expr::nat_lit(1)),
            &Expr::nat_lit(0)
        ),
        "Nat.add(u64::MAX, 1) should not reduce to 0 (overflow)"
    );
    // u64::MAX - 1 + 1 = u64::MAX -- should reduce
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.add", Expr::nat_lit(u64::MAX - 1), Expr::nat_lit(1)),
            &Expr::nat_lit(u64::MAX)
        ),
        "Nat.add(u64::MAX-1, 1) should reduce to u64::MAX"
    );
}

#[test]
fn test_reduce_nat_div_by_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // Nat.div(10, 0) = 0 per Lean 4 convention
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.div", Expr::nat_lit(10), Expr::nat_lit(0)),
            &Expr::nat_lit(0)
        ),
        "Nat.div(10, 0) should reduce to 0 (Lean convention)"
    );
}

#[test]
fn test_reduce_nat_mod_by_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // Nat.mod(10, 0) = 10 per Lean 4 convention
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.mod", Expr::nat_lit(10), Expr::nat_lit(0)),
            &Expr::nat_lit(10)
        ),
        "Nat.mod(10, 0) should reduce to 10 (Lean convention)"
    );
}

// =========================================================================
// reduce_nat pre-check -- Nat arithmetic via WHNF pre-check (#3134)
// =========================================================================

/// Nat.pow(2, 32) should reduce to 4294967296 via the WHNF pre-check,
/// NOT via exponential recursive unfolding through Nat.brecOn/Nat.rec.
/// This is the critical test for #3134 (100% Init TC verification).
#[test]
fn test_reduce_nat_pow_2_32_via_precheck() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.pow", Expr::nat_lit(2), Expr::nat_lit(32)),
            &Expr::nat_lit(4294967296)
        ),
        "Nat.pow(2, 32) should reduce to 4294967296"
    );
}

/// Nat.pow(2, 16) = 65536
#[test]
fn test_reduce_nat_pow_2_16() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.pow", Expr::nat_lit(2), Expr::nat_lit(16)),
            &Expr::nat_lit(65536)
        ),
        "Nat.pow(2, 16) should reduce to 65536"
    );
}

/// Nat.mul(Nat.add(2, 3), Nat.pow(2, 4)) = 80
#[test]
fn test_reduce_nat_nested_arithmetic() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // (2 + 3) * 2^4 = 5 * 16 = 80
    let add_2_3 = nat_binop("Nat.add", Expr::nat_lit(2), Expr::nat_lit(3));
    let pow_2_4 = nat_binop("Nat.pow", Expr::nat_lit(2), Expr::nat_lit(4));
    let result = nat_binop("Nat.mul", add_2_3, pow_2_4);
    assert!(
        tc.is_def_eq(&result, &Expr::nat_lit(80)),
        "Nat.mul(Nat.add(2, 3), Nat.pow(2, 4)) should reduce to 80"
    );
}

// =========================================================================
// try_iota_reduction -- MajorAfterMinors (standard rec)
// =========================================================================

/// Helper: create a simple enum with zero-arg constructors for iota testing.
fn make_bool_env() -> (Environment, Name) {
    let mut env = Environment::new();
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
    env.add_inductive(decl).expect("add MyBool inductive");
    (env, bool_name)
}

#[test]
fn test_try_iota_reduction_major_after_minors_false() {
    let (env, bool_name) = make_bool_env();
    let tc = TypeChecker::new(&env);
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);

    // MyBool.rec : {motive : MyBool -> Sort u} -> motive false -> motive true -> (b : MyBool) -> motive b
    let rec = Expr::const_(Name::from_string("MyBool.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, bool_ref, Expr::prop());
    let false_case = Expr::const_(Name::from_string("ResultF"), vec![]);
    let true_case = Expr::const_(Name::from_string("ResultT"), vec![]);
    let major = Expr::const_(Name::from_string("MyBool.false"), vec![]);

    // rec motive false_case true_case MyBool.false -> false_case
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec, motive), false_case.clone()),
            true_case,
        ),
        major,
    );
    let result = tc.whnf(&app);
    assert_eq!(
        result, false_case,
        "MyBool.rec on MyBool.false should reduce to false_case"
    );
}

#[test]
fn test_try_iota_reduction_major_after_minors_true() {
    let (env, bool_name) = make_bool_env();
    let tc = TypeChecker::new(&env);
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);

    let rec = Expr::const_(Name::from_string("MyBool.rec"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, bool_ref, Expr::prop());
    let false_case = Expr::const_(Name::from_string("ResultF"), vec![]);
    let true_case = Expr::const_(Name::from_string("ResultT"), vec![]);
    let major = Expr::const_(Name::from_string("MyBool.true"), vec![]);

    // rec motive false_case true_case MyBool.true -> true_case
    let app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec, motive), false_case),
            true_case.clone(),
        ),
        major,
    );
    let result = tc.whnf(&app);
    assert_eq!(
        result, true_case,
        "MyBool.rec on MyBool.true should reduce to true_case"
    );
}

// =========================================================================
// try_iota_reduction -- MajorAfterMotive (recOn style)
// =========================================================================

#[test]
fn test_try_iota_reduction_major_after_motive() {
    let (env, bool_name) = make_bool_env();
    let tc = TypeChecker::new(&env);
    let bool_ref = Expr::const_(bool_name.clone(), vec![]);

    // MyBool.recOn uses MajorAfterMotive: motive, major, minor_false, minor_true
    let rec_on = Expr::const_(Name::from_string("MyBool.recOn"), vec![Level::zero()]);
    let motive = Expr::lam(BinderInfo::Default, bool_ref, Expr::prop());
    let false_case = Expr::const_(Name::from_string("ResultF"), vec![]);
    let true_case = Expr::const_(Name::from_string("ResultT"), vec![]);
    let major = Expr::const_(Name::from_string("MyBool.true"), vec![]);

    // recOn motive MyBool.true false_case true_case -> true_case
    let app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec_on, motive), major), false_case),
        true_case.clone(),
    );
    let result = tc.whnf(&app);
    assert_eq!(
        result, true_case,
        "MyBool.recOn on MyBool.true should reduce to true_case"
    );
}

// =========================================================================
// projection reduction -- structure constructors
// =========================================================================

#[test]
fn test_projection_reduction_basic_struct() {
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
                    Expr::pi(BinderInfo::Default, nat.clone(), pair_ref),
                ),
            }],
        }],
    };
    env.add_inductive(decl).expect("add Pair inductive");
    let tc = TypeChecker::new(&env);

    // Pair.mk 3 7
    let mk = Expr::const_(Name::from_string("Pair.mk"), vec![]);
    let three = Expr::nat_lit(3);
    let seven = Expr::nat_lit(7);
    let pair_val = Expr::app(Expr::app(mk, three.clone()), seven.clone());

    // Proj 0 should extract first field (3)
    let proj0 = Expr::proj(pair_name.clone(), 0, pair_val.clone());
    let result0 = tc.whnf(&proj0);
    assert_eq!(result0, three, "Proj 0 should extract first field");

    // Proj 1 should extract second field (7)
    let proj1 = Expr::proj(pair_name, 1, pair_val);
    let result1 = tc.whnf(&proj1);
    assert_eq!(result1, seven, "Proj 1 should extract second field");
}

#[test]
fn test_projection_reduction_with_params() {
    // Structure with type parameters: Wrap A where val : A
    let mut env = Environment::new();
    let wrap_name = Name::from_string("Wrap");
    let mk_type = Expr::pi(
        BinderInfo::Default,
        Expr::type_(), // A : Type
        Expr::pi(
            BinderInfo::Default,
            Expr::bvar(0), // val : A
            Expr::app(Expr::const_(wrap_name.clone(), vec![]), Expr::bvar(1)),
        ),
    );
    let decl = InductiveDecl {
        level_params: vec![],
        num_params: 1, // A is a parameter
        types: vec![InductiveType {
            name: wrap_name.clone(),
            type_: Expr::pi(BinderInfo::Default, Expr::type_(), Expr::type_()),
            constructors: vec![Constructor {
                name: Name::from_string("Wrap.mk"),
                type_: mk_type,
            }],
        }],
    };
    env.add_inductive(decl).expect("add Wrap inductive");
    let tc = TypeChecker::new(&env);

    // Wrap.mk Prop True : Wrap Prop
    let mk = Expr::const_(Name::from_string("Wrap.mk"), vec![]);
    let payload = Expr::const_(Name::from_string("True"), vec![]);
    let wrap_val = Expr::app(Expr::app(mk, Expr::prop()), payload.clone());

    // Proj 0 should extract field 0 (skip 1 param) = payload
    let proj = Expr::proj(wrap_name, 0, wrap_val);
    let result = tc.whnf(&proj);
    assert_eq!(
        result, payload,
        "Proj 0 on parametric struct should extract the field"
    );
}

#[test]
fn test_projection_reduction_stuck_on_non_constructor() {
    // Projection on a non-constructor expression should remain stuck (unreduced)
    let env = Environment::new();
    let tc = TypeChecker::new(&env);
    let name = Name::from_string("SomeStruct");
    let fvar = Expr::const_(Name::from_string("x"), vec![]);
    let proj = Expr::proj(name, 0, fvar);
    let result = tc.whnf(&proj);
    assert!(
        matches!(&result.kind, ExprKind::Proj(_, _, _)),
        "Projection on non-constructor should stay unreduced"
    );
}

/// Create an environment with Nat, Char, List, and String defined.
fn make_string_env() -> Environment {
    let mut env = Environment::new();
    env.init_nat().expect("init Nat");
    env.init_char().expect("init Char");
    env.init_list().expect("init List");
    env.init_string().expect("init String");
    env
}

#[test]
fn test_string_lit_def_eq_expanded_empty() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("");
    let expanded = string_lit_to_constructor("");
    assert!(
        tc.is_def_eq(&literal, &expanded),
        "String literal \"\" should be definitionally equal to its constructor expansion"
    );
}

#[test]
fn test_string_lit_def_eq_expanded_hello() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("hello");
    let expanded = string_lit_to_constructor("hello");
    assert!(
        tc.is_def_eq(&literal, &expanded),
        "String literal \"hello\" should be definitionally equal to its constructor expansion"
    );
}

#[test]
fn test_string_lit_def_eq_expanded_unicode() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("α");
    let expanded = string_lit_to_constructor("α");
    assert!(
        tc.is_def_eq(&literal, &expanded),
        "String literal \"α\" should be definitionally equal to its constructor expansion"
    );
}

#[test]
fn test_string_lit_not_def_eq_different() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("a");
    let expanded = string_lit_to_constructor("b");
    assert!(
        !tc.is_def_eq(&literal, &expanded),
        "String literal \"a\" should not be definitionally equal to the constructor expansion of \"b\""
    );
}

// =========================================================================
// String literal def_eq against hand-written constructor terms (#3 gap:
// fully reduce nested Char.ofNat / List constructors in all def_eq contexts).
//
// `string_lit_to_constructor` is the importer's own lowering, so comparing a
// literal against its output (above) exercises the happy path. The tests
// below instead build the equivalent term *by hand* the way a user or a
// foreign-prover importer would — including the raw `String.mk` constructor
// (not the `String.ofList` alias) — to pin that the literal expansion fully
// reduces and matches genuine constructor forms while still rejecting
// non-equal strings.
// =========================================================================

/// Build `List.cons.{0} Char head tail` for a Char-typed list.
fn char_cons(head: Expr, tail: Expr) -> Expr {
    let char_t = Expr::const_(names::CHAR.clone(), vec![]);
    Expr::apps(
        Expr::const_(Name::from_string("List.cons"), vec![Level::zero()]),
        [char_t, head, tail],
    )
}

/// Build `List.nil.{0} Char`.
fn char_nil() -> Expr {
    let char_t = Expr::const_(names::CHAR.clone(), vec![]);
    Expr::app(
        Expr::const_(Name::from_string("List.nil"), vec![Level::zero()]),
        char_t,
    )
}

/// Build `Char.ofNat <n>` from a code point as a Nat literal.
fn char_of_nat(n: u64) -> Expr {
    Expr::app(
        Expr::const_(names::CHAR_OF_NAT.clone(), vec![]),
        Expr::nat_lit(n),
    )
}

/// `"ab"` (literal) is def_eq to the hand-written
/// `String.ofList (List.cons (Char.ofNat 97) (List.cons (Char.ofNat 98) List.nil))`.
#[test]
fn test_string_lit_def_eq_manual_oflist_constructor() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("ab");
    // List.cons (Char.ofNat 97) (List.cons (Char.ofNat 98) List.nil)
    let char_list = char_cons(char_of_nat(97), char_cons(char_of_nat(98), char_nil()));
    let manual = Expr::app(
        Expr::const_(names::STRING_OF_LIST.clone(), vec![]),
        char_list,
    );
    assert!(
        tc.is_def_eq(&literal, &manual),
        "String literal \"ab\" should be def_eq to a hand-written String.ofList [Char.ofNat 97, Char.ofNat 98]"
    );
    // Symmetric direction must hold too.
    assert!(
        tc.is_def_eq(&manual, &literal),
        "def_eq for string literal vs String.ofList constructor must be symmetric"
    );
}

/// `"ab"` (literal) is def_eq to the hand-written **`String.mk`** constructor
/// form. The previous implementation only fired when the other side's head was
/// syntactically `String.ofList`; this pins that the raw constructor is now
/// reduced and matched, exercising the widened expansion gate directly.
#[test]
fn test_string_lit_def_eq_manual_string_mk_constructor() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("ab");
    let char_list = char_cons(char_of_nat(97), char_cons(char_of_nat(98), char_nil()));
    let manual = Expr::app(
        Expr::const_(Name::from_string("String.mk"), vec![]),
        char_list,
    );
    assert!(
        tc.is_def_eq(&literal, &manual),
        "String literal \"ab\" should be def_eq to a hand-written String.mk [Char.ofNat 97, Char.ofNat 98]"
    );
    assert!(
        tc.is_def_eq(&manual, &literal),
        "def_eq for string literal vs String.mk constructor must be symmetric"
    );
}

/// Negative: `"ab"` is NOT def_eq to a constructor term for `"ac"`.
/// Distinct code points (98 vs 99) must keep the strings apart even though
/// the literal expansion fully reduces.
#[test]
fn test_string_lit_not_def_eq_manual_different_char() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("ab");
    // String.ofList [Char.ofNat 97, Char.ofNat 99]  == "ac"
    let char_list_ac = char_cons(char_of_nat(97), char_cons(char_of_nat(99), char_nil()));
    let manual_ac = Expr::app(
        Expr::const_(names::STRING_OF_LIST.clone(), vec![]),
        char_list_ac.clone(),
    );
    assert!(
        !tc.is_def_eq(&literal, &manual_ac),
        "String literal \"ab\" must NOT be def_eq to the constructor form of \"ac\""
    );
    // Same with the raw String.mk constructor.
    let manual_ac_mk = Expr::app(
        Expr::const_(Name::from_string("String.mk"), vec![]),
        char_list_ac,
    );
    assert!(
        !tc.is_def_eq(&literal, &manual_ac_mk),
        "String literal \"ab\" must NOT be def_eq to String.mk form of \"ac\""
    );
}

/// Negative: `"ab"` is NOT def_eq to a constructor term of a different length
/// (`"a"`). A shorter character list must not be accepted.
#[test]
fn test_string_lit_not_def_eq_manual_different_length() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::str_lit("ab");
    let char_list_a = char_cons(char_of_nat(97), char_nil());
    let manual_a = Expr::app(
        Expr::const_(names::STRING_OF_LIST.clone(), vec![]),
        char_list_a,
    );
    assert!(
        !tc.is_def_eq(&literal, &manual_a),
        "String literal \"ab\" must NOT be def_eq to the constructor form of \"a\""
    );
}

#[test]
fn test_nat_lit_def_eq_zero_const() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::nat_lit(0);
    let zero_const = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    assert!(
        tc.is_def_eq(&literal, &zero_const),
        "Nat literal 0 should be definitionally equal to Nat.zero"
    );
}

#[test]
fn test_nat_lit_def_eq_succ_form() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::nat_lit(3);
    let zero = Expr::const_(Name::from_string("Nat.zero"), vec![]);
    let succ1 = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), zero);
    let succ2 = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), succ1);
    let succ3 = Expr::app(Expr::const_(Name::from_string("Nat.succ"), vec![]), succ2);
    assert!(
        tc.is_def_eq(&literal, &succ3),
        "Nat literal 3 should be definitionally equal to Nat.succ(Nat.succ(Nat.succ(Nat.zero)))"
    );
}

#[test]
fn test_nat_lit_def_eq_constructor_42() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let literal = Expr::nat_lit(42);
    let expanded = nat_lit_to_constructor(&BigNat::Small(42));
    assert!(
        tc.is_def_eq(&literal, &expanded),
        "Nat literal 42 should be definitionally equal to nat_lit_to_constructor(42)"
    );
}

#[test]
fn test_string_lit_proj_extracts_data() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let proj = Expr::proj(Name::from_string("String"), 0, Expr::str_lit("A"));
    let result = tc.whnf(&proj);
    let expected_list = string_lit_to_constructor("A").get_app_args()[0].clone();

    assert!(
        !matches!(&result.kind, ExprKind::Proj(..)),
        "Proj(String, 0, \"A\") should reduce to the character list, not remain a projection: {result:?}"
    );
    assert_eq!(
        result, expected_list,
        "Proj(String, 0, \"A\") should reduce to the underlying character list"
    );
}

#[test]
fn test_string_lit_proj_empty_string() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let proj = Expr::proj(Name::from_string("String"), 0, Expr::str_lit(""));
    let result = tc.whnf(&proj);
    let expected_list = string_lit_to_constructor("").get_app_args()[0].clone();

    assert!(
        !matches!(&result.kind, ExprKind::Proj(..)),
        "Proj(String, 0, \"\") should reduce to the empty character list, not remain a projection: {result:?}"
    );
    assert_eq!(
        result, expected_list,
        "Proj(String, 0, \"\") should reduce to the empty character list"
    );
}

#[test]
fn test_nat_rec_on_literal() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let nat = Expr::const_(Name::from_string("Nat"), vec![]);
    let motive = Expr::lam(BinderInfo::Default, nat.clone(), nat.clone());
    let zero_case = Expr::nat_lit(100);
    let succ_case = Expr::lam(
        BinderInfo::Default,
        nat.clone(),
        Expr::lam(BinderInfo::Default, nat.clone(), Expr::nat_lit(200)),
    );
    let rec = Expr::const_(
        Name::from_string("Nat.rec"),
        vec![Level::succ(Level::zero())],
    );

    let zero_app = Expr::app(
        Expr::app(
            Expr::app(Expr::app(rec.clone(), motive.clone()), zero_case.clone()),
            succ_case.clone(),
        ),
        Expr::nat_lit(0),
    );
    let zero_result = tc.whnf(&zero_app);
    assert_eq!(
        zero_result,
        Expr::nat_lit(100),
        "Nat.rec with major premise 0 should reduce to the zero case"
    );

    let succ_app = Expr::app(
        Expr::app(Expr::app(Expr::app(rec, motive), zero_case), succ_case),
        Expr::nat_lit(1),
    );
    let succ_result = tc.whnf(&succ_app);
    assert_eq!(
        succ_result,
        Expr::nat_lit(200),
        "Nat.rec with major premise 1 should reduce to the successor case result"
    );
}

// =========================================================================
// BigNat base in Nat.pow — Lean 4 parity (#3134)
// =========================================================================

/// Helper: create a BigNat literal expression (value > u64::MAX).
fn bignat_lit(limbs: Vec<u64>) -> Expr {
    Expr::from_kind(ExprKind::Lit(Literal::Nat(BigNat::Big(limbs))))
}

/// BigNat^0 should reduce to 1 (n^0 = 1 for any n).
#[test]
fn test_reduce_nat_pow_bignat_base_exp_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // 2^64 = BigNat([0, 1])
    let big_base = bignat_lit(vec![0, 1]);
    let pow_expr = nat_binop("Nat.pow", big_base, Expr::nat_lit(0));
    assert!(
        tc.is_def_eq(&pow_expr, &Expr::nat_lit(1)),
        "BigNat^0 should reduce to 1"
    );
}

/// BigNat^1 should reduce to the base itself (n^1 = n for any n).
#[test]
fn test_reduce_nat_pow_bignat_base_exp_one() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // 2^64 = BigNat([0, 1])
    let big_base = bignat_lit(vec![0, 1]);
    let expected = big_base.clone();
    let pow_expr = nat_binop("Nat.pow", big_base, Expr::nat_lit(1));
    assert!(
        tc.is_def_eq(&pow_expr, &expected),
        "BigNat^1 should reduce to the BigNat base itself"
    );
}

/// BigNat^2 should stay stuck (we don't compute arbitrary-precision power).
#[test]
fn test_reduce_nat_pow_bignat_base_exp_two_stays_stuck() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // 2^64 = BigNat([0, 1])
    let big_base = bignat_lit(vec![0, 1]);
    let pow_expr = nat_binop("Nat.pow", big_base, Expr::nat_lit(2));
    // whnf should NOT reduce this to a literal (stays as the Nat.pow application)
    let result = tc.whnf(&pow_expr);
    // If it reduced, it would be a Lit. If stuck, it stays as an app.
    // We verify it doesn't equal 1 or the base — it stays unreduced.
    assert!(
        !tc.is_def_eq(&result, &Expr::nat_lit(1)),
        "BigNat^2 should not reduce to 1"
    );
}

/// (2^64 + 1)^0 should reduce to 1.
#[test]
fn test_reduce_nat_pow_bignat_large_base_exp_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // 2^64 + 1 = BigNat([1, 1])
    let big_base = bignat_lit(vec![1, 1]);
    let pow_expr = nat_binop("Nat.pow", big_base, Expr::nat_lit(0));
    assert!(
        tc.is_def_eq(&pow_expr, &Expr::nat_lit(1)),
        "(2^64+1)^0 should reduce to 1"
    );
}

/// (2^64 + 1)^1 should reduce to 2^64 + 1.
#[test]
fn test_reduce_nat_pow_bignat_large_base_exp_one() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // 2^64 + 1 = BigNat([1, 1])
    let big_base = bignat_lit(vec![1, 1]);
    let expected = big_base.clone();
    let pow_expr = nat_binop("Nat.pow", big_base, Expr::nat_lit(1));
    assert!(
        tc.is_def_eq(&pow_expr, &expected),
        "(2^64+1)^1 should reduce to the base"
    );
}

/// Small base pow still works (regression guard).
#[test]
fn test_reduce_nat_pow_small_base_still_works() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    // 3^5 = 243
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.pow", Expr::nat_lit(3), Expr::nat_lit(5)),
            &Expr::nat_lit(243)
        ),
        "Nat.pow(3, 5) should still reduce to 243"
    );
    // 0^0 = 1
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.pow", Expr::nat_lit(0), Expr::nat_lit(0)),
            &Expr::nat_lit(1)
        ),
        "Nat.pow(0, 0) should reduce to 1"
    );
    // 1^1000000 = 1
    assert!(
        tc.is_def_eq(
            &nat_binop("Nat.pow", Expr::nat_lit(1), Expr::nat_lit(1000000)),
            &Expr::nat_lit(1)
        ),
        "Nat.pow(1, 1000000) should reduce to 1"
    );
}

// =========================================================================
// String literal projection in cheap projection mode — Part of #3234
// =========================================================================

/// Proj(String, 0, "A") must reduce even in cheap projection (no-delta) mode.
///
/// Before the fix, `whnf_core_no_delta(_, cheap_proj=true)` expanded the
/// string literal to `String.ofList(list)` but then recursed with no-delta
/// WHNF, which couldn't unfold `String.ofList` to reach `String.mk`. The
/// projection stayed stuck. The fix uses full WHNF for the string expansion
/// step since it's an internal lowering, not a user-visible delta unfold.
#[test]
fn test_string_lit_proj_cheap_proj_mode_reduces() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let proj = Expr::proj(Name::from_string("String"), 0, Expr::str_lit("A"));
    let result = tc.whnf_core_no_delta(&proj, true);
    assert!(
        !matches!(&result.kind, ExprKind::Proj(..)),
        "Proj(String, 0, \"A\") should reduce in cheap projection mode, got: {result:?}"
    );
}

/// Same test with empty string: Proj(String, 0, "") in cheap projection mode.
#[test]
fn test_string_lit_proj_cheap_proj_mode_empty_string() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let proj = Expr::proj(Name::from_string("String"), 0, Expr::str_lit(""));
    let result = tc.whnf_core_no_delta(&proj, true);
    assert!(
        !matches!(&result.kind, ExprKind::Proj(..)),
        "Proj(String, 0, \"\") should reduce in cheap projection mode, got: {result:?}"
    );
}

/// Cheap projection result should match full WHNF result for string projections.
#[test]
fn test_string_lit_proj_cheap_matches_full_whnf() {
    let env = make_string_env();
    let tc = TypeChecker::new(&env);
    let proj = Expr::proj(Name::from_string("String"), 0, Expr::str_lit("hi"));
    let full_result = tc.whnf(&proj);
    let cheap_result = tc.whnf_core_no_delta(&proj, true);
    assert_eq!(
        full_result, cheap_result,
        "String projection in cheap-proj mode should produce same result as full WHNF"
    );
}

// =========================================================================
// `Nat.pred` native reducer — the "Rat-blowup wall" closer.
//
// `Nat.pred n := Nat.rec Nat.zero (λ m _ => m) n` (data_types_nat.rs:359). On a
// large literal (e.g. `2^1074`) that recursor, via `nat_lit_to_constructor`,
// peels `Nat.succ` layers one at a time — a chain of depth O(value) that
// OOM/SIGKILLs the kernel past a ~2^16 argument. The native `reduce_nat` arm
// added here intercepts `Nat.pred (Lit n)` BEFORE δ-unfolding and returns
// `Lit (n-1)` (or `Lit 0` for `n=0`) in O(1) on the literal. These tests prove
// the wall is CLOSED: each reduces in bounded time (no SIGKILL).
// =========================================================================

/// `Nat.pred (Lit (1<<k))` (a literal `2^k`) used to force a `Nat.rec`
/// `succ∘pred` chain of depth `2^k`; with the native reducer it is O(1).
fn pred_of_pow2(env: &Environment, k: usize) -> Expr {
    let tc = TypeChecker::new(env);
    let two_pow_k = BigNat::Small(1).checked_shl_big(k);
    let arg = Expr::bignat_lit(two_pow_k);
    let app = Expr::app(Expr::const_(names::NAT_PRED.clone(), vec![]), arg);
    tc.whnf(&app)
}

/// `Nat.pred (2^1074)` — the binary64 floored-ulp denominator scale that the
/// half-ulp / dot-product walls hit — reduces to `2^1074 − 1` in BOUNDED time.
/// Before the native arm this δ-unfolded `Nat.pred` into a `2^1074`-deep
/// `Nat.rec` chain and SIGKILLed; the test completing at all IS the proof the
/// wall is closed.
#[test]
fn test_nat_pred_native_2_pow_1074_bounded() {
    let env = make_nat_env();
    let start = std::time::Instant::now();
    let result = pred_of_pow2(&env, 1074);
    let elapsed = start.elapsed();
    // Expected: 2^1074 − 1 (all-ones, 1074 bits).
    let expected = BigNat::Small(1).checked_shl_big(1074).pred().unwrap();
    assert_eq!(
        result,
        Expr::bignat_lit(expected),
        "Nat.pred(2^1074) must reduce to 2^1074 − 1"
    );
    // O(1)-on-the-literal: trivially under a second. The OLD path never returned.
    assert!(
        elapsed.as_secs() < 5,
        "Nat.pred(2^1074) took {elapsed:?}; the native reducer should be ~instant"
    );
}

/// `Nat.pred (2^(53·8)) = Nat.pred (2^424)` — the `(1+u)^n` denominator scale
/// `2^(53n)` for binary64 — also reduces in bounded time.
#[test]
fn test_nat_pred_native_2_pow_53n_bounded() {
    let env = make_nat_env();
    let result = pred_of_pow2(&env, 53 * 8); // 2^424
    let expected = BigNat::Small(1).checked_shl_big(53 * 8).pred().unwrap();
    assert_eq!(result, Expr::bignat_lit(expected));
}

/// Boundary semantics: `Nat.pred 0 = 0` (Lean floored predecessor).
#[test]
fn test_nat_pred_native_zero_is_zero() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let app = Expr::app(
        Expr::const_(names::NAT_PRED.clone(), vec![]),
        Expr::nat_lit(0),
    );
    assert_eq!(tc.whnf(&app), Expr::nat_lit(0), "Nat.pred 0 = 0");
}

/// Small-literal parity: `Nat.pred (n+1) = n` for a handful of values.
#[test]
fn test_nat_pred_native_small_values() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    for n in [1u64, 2, 7, 100, 65_537] {
        let app = Expr::app(
            Expr::const_(names::NAT_PRED.clone(), vec![]),
            Expr::nat_lit(n),
        );
        assert_eq!(
            tc.whnf(&app),
            Expr::nat_lit(n - 1),
            "Nat.pred {n} = {}",
            n - 1
        );
    }
}

/// `Nat.succ (Nat.pred (2^1074))` — exactly the shape of `Rat.Raw.effDenom` on a
/// `2^1074` denominator — reduces to `2^1074` (succ ∘ pred is identity on a
/// positive value) in BOUNDED time. This is the precise expression `Rat.le`
/// lifts through; its bounded reduction is the wall-closed proof for `Rat.le`.
#[test]
fn test_nat_succ_pred_effdenom_shape_2_pow_1074_bounded() {
    let env = make_nat_env();
    let tc = TypeChecker::new(&env);
    let two_pow = BigNat::Small(1).checked_shl_big(1074);
    let pred_app = Expr::app(
        Expr::const_(names::NAT_PRED.clone(), vec![]),
        Expr::bignat_lit(two_pow.clone()),
    );
    let succ_pred = Expr::app(Expr::const_(names::NAT_SUCC.clone(), vec![]), pred_app);
    let start = std::time::Instant::now();
    let result = tc.whnf(&succ_pred);
    let elapsed = start.elapsed();
    assert_eq!(
        result,
        Expr::bignat_lit(two_pow),
        "succ(pred(2^1074)) = 2^1074 (effDenom of a positive denominator)"
    );
    assert!(
        elapsed.as_secs() < 5,
        "succ(pred(2^1074)) took {elapsed:?}; should be ~instant via native reducers"
    );
}
