// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Source-to-term regressions for parameters before the decreasing argument.
//!
//! Kernel checking alone cannot detect a recursive-call elaboration that drops
//! a changed accumulator: the resulting constant-accumulator function still
//! has the declared type. These tests elaborate the actual surface definition,
//! recheck its stored kernel value, and test the resulting computation.

use clean_elab::elaborate_decl_and_register;
use clean_kernel::{Environment, Expr, Name, TypeChecker};
use clean_parser::parse_decl;

fn nat_environment() -> Environment {
    let mut env = Environment::new();
    env.init_nat()
        .expect("the actual Nat declarations must check");
    env
}

fn recheck_stored_definition(env: &Environment, name: &str) {
    let constant = env
        .get_const(&Name::from_string(name))
        .expect("successful public registration must store the definition");
    let value = constant
        .value
        .as_ref()
        .expect("the surface definition must produce an actual kernel value");
    TypeChecker::new(env)
        .check_type(value, &constant.type_)
        .expect("the actual stored value must independently type-check");
}

fn register(env: &mut Environment, name: &str, source: &str) {
    let decl = parse_decl(source).expect("the regression source must parse");
    elaborate_decl_and_register(env, &decl)
        .expect("valid structural recursion must elaborate and register");
    recheck_stored_definition(env, name);
}

fn assert_application(env: &Environment, name: &str, args: &[u64], expected: u64) {
    let application = args.iter().fold(
        Expr::const_(Name::from_string(name), vec![]),
        |function, argument| Expr::app(function, Expr::nat_lit(*argument)),
    );
    let checker = TypeChecker::new(env);
    checker
        .check_type(
            &application,
            &Expr::const_(Name::from_string("Nat"), vec![]),
        )
        .expect("the actual caller must be a well-typed Nat expression");
    let reduced = checker.whnf(&application);
    assert!(
        checker.is_def_eq(&reduced, &Expr::nat_lit(expected)),
        "{name}{args:?} must compute to {expected}; actual kernel WHNF: {reduced:?}"
    );
}

fn reject(env: &mut Environment, name: &str, source: &str) {
    let decl = parse_decl(source).expect("the negative control must parse");
    assert!(
        elaborate_decl_and_register(env, &decl).is_err(),
        "ill-typed recursive source {name} must not be accepted"
    );
    assert!(env.get_const(&Name::from_string(name)).is_none());
}

fn prefix_list_environment() -> Environment {
    let mut env = nat_environment();
    let declaration = parse_decl(
        "inductive PrefixList (A : Type) : Type where\n| nil : PrefixList A\n| cons : A -> PrefixList A -> PrefixList A",
    )
    .expect("the actual parameterized inductive source must parse");
    elaborate_decl_and_register(&mut env, &declaration)
        .expect("the actual parameterized inductive must register");
    env
}

fn prefix_vec_environment() -> Environment {
    let mut env = nat_environment();
    let declaration = parse_decl(
        "inductive PrefixVec (A : Type) : Nat -> Type where\n| nil : PrefixVec A Nat.zero\n| cons : (n : Nat) -> A -> PrefixVec A n -> PrefixVec A (Nat.succ n)",
    )
    .expect("the actual indexed inductive must parse");
    elaborate_decl_and_register(&mut env, &declaration)
        .expect("the actual indexed inductive must register");
    env
}

#[test]
fn changed_prefix_parameter_is_not_erased() {
    let mut env = nat_environment();
    register(
        &mut env,
        "prefixAccum",
        r"def prefixAccum (acc : Nat) (n : Nat) : Nat := match n with
| Nat.zero => acc
| Nat.succ k => prefixAccum (Nat.succ acc) k",
    );
    assert_application(&env, "prefixAccum", &[0, 2], 2);
    assert_application(&env, "prefixAccum", &[3, 2], 5);
}

#[test]
fn qualified_lookalike_heads_are_not_recursive_calls() {
    let mut env = nat_environment();
    reject(
        &mut env,
        "badQualified",
        r"def badQualified (n : Nat) : Nat := match n with
| Nat.zero => 0
| Nat.succ k => Nat.add (badQualified k) (Bogus.badQualified k)",
    );
    reject(
        &mut env,
        "PrefixNames.Inner.badRoot",
        r"def PrefixNames.Inner.badRoot (n : Nat) : Nat := match n with
| Nat.zero => 0
| Nat.succ k => Nat.add (PrefixNames.Inner.badRoot k) (_root_.Inner.badRoot k)",
    );
}

#[test]
fn namespace_relative_and_exact_root_calls_keep_computation() {
    let mut env = nat_environment();
    let decl = parse_decl(
        r"namespace PrefixNames
def Inner.relative (n : Nat) : Nat := match n with
| Nat.zero => 1
| Nat.succ k => Nat.succ (Inner.relative k)
def Inner.rooted (n : Nat) : Nat := match n with
| Nat.zero => 1
| Nat.succ k => Nat.succ (_root_.PrefixNames.Inner.rooted k)
end PrefixNames",
    )
    .expect("namespace-relative controls must parse");
    elaborate_decl_and_register(&mut env, &decl).expect("namespace must elaborate");
    for name in ["PrefixNames.Inner.relative", "PrefixNames.Inner.rooted"] {
        recheck_stored_definition(&env, name);
        assert_application(&env, name, &[2], 3);
    }
}

#[test]
fn qualified_receiver_shadowing_does_not_become_recursion() {
    let mut env = nat_environment();
    reject(
        &mut env,
        "PrefixNames.shadow",
        r"def PrefixNames.shadow (n : Nat) : Nat := match n with
| Nat.zero => 0
| Nat.succ k => Nat.add (PrefixNames.shadow k) ((fun (PrefixNames : Nat) => PrefixNames.shadow k) 0)",
    );
    register(&mut env, "ReceiverValue", "def ReceiverValue : Nat := 0");
    reject(
        &mut env,
        "ReceiverValue.recur",
        r"def ReceiverValue.recur (n : Nat) : Nat := match n with
| Nat.zero => 0
| Nat.succ k => Nat.add (_root_.ReceiverValue.recur k) (ReceiverValue.recur k)",
    );
}

#[test]
fn an_existing_suffix_named_global_keeps_its_own_computation() {
    let mut env = nat_environment();
    register(
        &mut env,
        "Inner.suffix",
        "def Inner.suffix (n : Nat) : Nat := 37",
    );
    register(
        &mut env,
        "Outer.Inner.suffix",
        r"def Outer.Inner.suffix (n : Nat) : Nat := match n with
| Nat.zero => 0
| Nat.succ k => Nat.add (Outer.Inner.suffix k) (Inner.suffix k)",
    );
    assert_application(&env, "Outer.Inner.suffix", &[1], 37);
    assert_application(&env, "Outer.Inner.suffix", &[2], 74);
    register(
        &mut env,
        "Inner.priority",
        "def Inner.priority (n : Nat) : Nat := 59",
    );
    let decl = parse_decl(
        r"namespace Outer
def Inner.priority (n : Nat) : Nat := match n with
| Nat.zero => 1
| Nat.succ k => Nat.succ (Inner.priority k)
end Outer",
    )
    .expect("pending namespace-member priority must parse");
    elaborate_decl_and_register(&mut env, &decl).expect("namespace must elaborate");
    recheck_stored_definition(&env, "Outer.Inner.priority");
    assert_application(&env, "Outer.Inner.priority", &[2], 3);
}

#[test]
fn dependent_prefix_telescope_can_change_together() {
    let mut env = nat_environment();
    register(
        &mut env,
        "dependentPrefix",
        r"def dependentPrefix (A : Type) (x : A) (read : A -> Nat) (n : Nat) : Nat := match n with
| Nat.zero => read x
| Nat.succ k => dependentPrefix Nat 7 (fun (y : Nat) => y) k",
    );
    register(
        &mut env,
        "dependentCaller",
        r"def dependentCaller : Nat := dependentPrefix (Nat -> Nat) (fun (x : Nat) => x) (fun (f : Nat -> Nat) => f 3) 2",
    );
    assert_application(&env, "dependentCaller", &[], 7);
}

#[test]
fn dependent_changed_prefix_is_checked_at_the_new_type() {
    let mut env = nat_environment();
    reject(
        &mut env,
        "badDependentPrefix",
        r"def badDependentPrefix (A : Type) (x : A) (n : Nat) : Nat := match n with
| Nat.zero => 0
| Nat.succ k => badDependentPrefix Nat (fun (y : Nat) => y) k",
    );
}

#[test]
fn inferred_implicit_prefix_can_change_with_dependent_arguments() {
    let mut env = nat_environment();
    register(
        &mut env,
        "implicitPrefix",
        r"def implicitPrefix {A : Type} (x : A) (read : A -> Nat) (n : Nat) : Nat := match n with
| Nat.zero => read x
| Nat.succ k => implicitPrefix (7 : Nat) (fun (y : Nat) => y) k",
    );
    register(
        &mut env,
        "implicitCaller",
        r"def implicitCaller : Nat := @implicitPrefix (Nat -> Nat) (fun (x : Nat) => x) (fun (f : Nat -> Nat) => f 3) 2",
    );
    assert_application(&env, "implicitCaller", &[], 7);
}

#[test]
fn fixed_type_parameter_and_movable_prefix_coexist() {
    let mut env = prefix_list_environment();
    register(
        &mut env,
        "mixedPrefix",
        r"def mixedPrefix (A : Type) (acc : Nat) (xs : PrefixList A) : Nat := match xs with
| PrefixList.nil => acc
| PrefixList.cons x tail => mixedPrefix A (Nat.succ acc) tail",
    );
    register(
        &mut env,
        "mixedCaller",
        r"def mixedCaller : Nat := mixedPrefix Nat 3 (@PrefixList.cons Nat 7 (@PrefixList.cons Nat 8 (@PrefixList.nil Nat)))",
    );
    assert_application(&env, "mixedCaller", &[], 5);
}

#[test]
fn erased_fixed_prefix_is_still_type_checked() {
    let mut env = prefix_list_environment();
    reject(
        &mut env,
        "badFixedPrefix",
        r"def badFixedPrefix (A : Type) (xs : PrefixList A) : Nat := match xs with
| PrefixList.nil => 0
| PrefixList.cons x tail => badFixedPrefix (fun (y : Nat) => y) tail",
    );
}

#[test]
fn parameters_are_captured_before_pattern_name_shadowing() {
    let mut env = nat_environment();
    register(
        &mut env,
        "shadowPrefix",
        r"def shadowPrefix (acc : Nat) (n : Nat) : Nat := match n with
| Nat.zero => acc
| Nat.succ acc => shadowPrefix (Nat.succ acc) acc",
    );
    assert_application(&env, "shadowPrefix", &[9, 2], 1);
}

#[test]
fn shadowed_major_is_not_the_constructor_fields_ih() {
    let mut env = nat_environment();
    reject(
        &mut env,
        "shadowedMajor",
        r"def shadowedMajor (acc : Nat) (n : Nat) : Nat := match n with
| Nat.zero => acc
| Nat.succ k => (fun (k : Nat) => shadowedMajor (Nat.succ acc) k) 100",
    );
}

#[test]
fn a_shadowed_match_discriminant_cannot_supply_structural_ihs() {
    let mut env = nat_environment();
    reject(
        &mut env,
        "reboundMajor",
        r"def reboundMajor (n : Nat) : Nat := (fun (n : Nat) => match n with
| Nat.zero => 0
| Nat.succ k => Nat.succ (reboundMajor k)) 2",
    );
}

#[test]
fn a_locally_shadowed_function_name_is_an_ordinary_call() {
    let mut env = nat_environment();
    register(
        &mut env,
        "shadowedHead",
        r"def shadowedHead (acc : Nat) (n : Nat) : Nat := match n with
| Nat.zero => acc
| Nat.succ k => (fun (shadowedHead : Nat -> Nat -> Nat) => shadowedHead 9 k) (fun (x : Nat) (y : Nat) => x)",
    );
    assert_application(&env, "shadowedHead", &[0, 2], 9);
}

#[test]
fn indexed_major_indices_vary_but_uniform_parameters_stay_fixed() {
    let mut env = prefix_vec_environment();
    register(
        &mut env,
        "indexedPrefix",
        r"def indexedPrefix (A : Type) (acc : Nat) (n : Nat) (xs : PrefixVec A n) : Nat := match xs with
| PrefixVec.nil => acc
| PrefixVec.cons m x tail => indexedPrefix A (Nat.succ acc) m tail",
    );
    register(
        &mut env,
        "indexedCaller",
        r"def indexedCaller : Nat := indexedPrefix Nat 3 2 (@PrefixVec.cons Nat 1 7 (@PrefixVec.cons Nat 0 8 (@PrefixVec.nil Nat)))",
    );
    assert_application(&env, "indexedCaller", &[], 5);
    register(
        &mut env,
        "implicitIndexedPrefix",
        r"def implicitIndexedPrefix (A : Type) (acc : Nat) {n : Nat} (xs : PrefixVec A n) : Nat := match xs with
| PrefixVec.nil => acc
| PrefixVec.cons m x tail => implicitIndexedPrefix A (Nat.succ acc) tail",
    );
    register(
        &mut env,
        "implicitIndexedCaller",
        r"def implicitIndexedCaller : Nat := @implicitIndexedPrefix Nat 3 2 (@PrefixVec.cons Nat 1 7 (@PrefixVec.cons Nat 0 8 (@PrefixVec.nil Nat)))",
    );
    assert_application(&env, "implicitIndexedCaller", &[], 5);
}

#[test]
fn recursive_index_arguments_are_observable_and_not_discarded() {
    let mut env = prefix_vec_environment();
    register(
        &mut env,
        "observedIndex",
        r"def observedIndex (n : Nat) (xs : PrefixVec Nat n) : Nat := match xs with
| PrefixVec.nil => n
| PrefixVec.cons m x tail => observedIndex m tail",
    );
    register(
        &mut env,
        "observedIndexCaller",
        "def observedIndexCaller : Nat := observedIndex 2 (@PrefixVec.cons Nat 1 7 (@PrefixVec.cons Nat 0 8 (@PrefixVec.nil Nat)))",
    );
    assert_application(&env, "observedIndexCaller", &[], 0);
}

#[test]
fn recursive_major_observations_use_the_current_constructor() {
    let mut env = nat_environment();
    register(
        &mut env,
        "observedMajor",
        r"def observedMajor (n : Nat) : Nat := match n with
| Nat.zero => n
| Nat.succ k => observedMajor k",
    );
    assert_application(&env, "observedMajor", &[2], 0);
    register(
        &mut env,
        "observedCatchAll",
        r"def observedCatchAll (n : Nat) : Nat := match n with
| Nat.succ k => observedCatchAll k
| _ => n",
    );
    assert_application(&env, "observedCatchAll", &[2], 0);
    register(
        &mut env,
        "observedNamedCatchAll",
        r"def observedNamedCatchAll (n : Nat) : Nat := match n with
| Nat.succ k => observedNamedCatchAll k
| x => x",
    );
    assert_application(&env, "observedNamedCatchAll", &[2], 0);
}

#[test]
fn internal_index_aliases_do_not_shadow_real_parameter_names() {
    let mut env = prefix_vec_environment();
    register(
        &mut env,
        "internalPrefix",
        r"def internalPrefix (_recursive_index : Nat) (n : Nat) (xs : PrefixVec Nat n) : Nat := match xs with
| PrefixVec.nil => _recursive_index
| PrefixVec.cons n x tail => internalPrefix (Nat.succ _recursive_index) n tail",
    );
    register(
        &mut env,
        "internalPrefixCaller",
        "def internalPrefixCaller : Nat := internalPrefix 19 2 (@PrefixVec.cons Nat 1 7 (@PrefixVec.cons Nat 0 8 (@PrefixVec.nil Nat)))",
    );
    assert_application(&env, "internalPrefixCaller", &[], 21);
    register(
        &mut env,
        "_recursive_index",
        "def _recursive_index : Nat := 37",
    );
    register(
        &mut env,
        "globalPrefix",
        r"def globalPrefix (n : Nat) (xs : PrefixVec Nat n) : Nat := match xs with
| PrefixVec.nil => 0
| PrefixVec.cons n x tail => Nat.add _recursive_index (globalPrefix n tail)",
    );
    register(
        &mut env,
        "globalPrefixCaller",
        "def globalPrefixCaller : Nat := globalPrefix 2 (@PrefixVec.cons Nat 1 7 (@PrefixVec.cons Nat 0 8 (@PrefixVec.nil Nat)))",
    );
    assert_application(&env, "globalPrefixCaller", &[], 74);
}

#[test]
fn nonrecursive_dependent_index_result_remains_supported() {
    let mut env = prefix_vec_environment();
    register(
        &mut env,
        "rebuildIndex",
        r"def rebuildIndex (n : Nat) (xs : PrefixVec Nat n) : PrefixVec Nat n := match xs with
| PrefixVec.nil => @PrefixVec.nil Nat
| PrefixVec.cons m x tail => @PrefixVec.cons Nat m x tail",
    );
    register(
        &mut env,
        "rebuildIndexCaller",
        "def rebuildIndexCaller : PrefixVec Nat 1 := rebuildIndex 1 (@PrefixVec.cons Nat 0 7 (@PrefixVec.nil Nat))",
    );
}

#[test]
fn recursive_dependent_index_result_uses_the_actual_index() {
    let mut env = prefix_vec_environment();
    register(
        &mut env,
        "recursiveRebuildIndex",
        r"def recursiveRebuildIndex (n : Nat) (xs : PrefixVec Nat n) : PrefixVec Nat n := match xs with
| PrefixVec.nil => @PrefixVec.nil Nat
| PrefixVec.cons m x tail => @PrefixVec.cons Nat m x (recursiveRebuildIndex m tail)",
    );
    register(
        &mut env,
        "recursiveRebuildIndexCaller",
        "def recursiveRebuildIndexCaller : PrefixVec Nat 2 := recursiveRebuildIndex 2 (@PrefixVec.cons Nat 1 7 (@PrefixVec.cons Nat 0 8 (@PrefixVec.nil Nat)))",
    );
    register(
        &mut env,
        "recursiveRebuildIndexExpected",
        "def recursiveRebuildIndexExpected : PrefixVec Nat 2 := @PrefixVec.cons Nat 1 7 (@PrefixVec.cons Nat 0 8 (@PrefixVec.nil Nat))",
    );
    assert!(TypeChecker::new(&env).is_def_eq(
        &Expr::const_(Name::from_string("recursiveRebuildIndexCaller"), vec![]),
        &Expr::const_(Name::from_string("recursiveRebuildIndexExpected"), vec![]),
    ));
}

#[test]
fn recursive_function_result_arguments_are_not_discarded() {
    let mut env = nat_environment();
    register(
        &mut env,
        "functionPrefix",
        r"def functionPrefix (acc : Nat) (n : Nat) : Nat -> Nat := match n with
| Nat.zero => fun (x : Nat) => x
| Nat.succ k => fun (x : Nat) => functionPrefix (Nat.succ acc) k (Nat.succ x)",
    );
    assert_application(&env, "functionPrefix", &[0, 2, 3], 5);
}

#[test]
fn returned_function_arguments_constrain_declaration_implicits_before_defaulting() {
    let mut env = nat_environment();
    register(
        &mut env,
        "resultImplicit",
        r"def resultImplicit {A : Type} (n : Nat) : A -> Nat := match n with
| Nat.zero => fun (x : A) => 0
| Nat.succ k => fun (x : A) => resultImplicit k (7 : Nat)",
    );
    register(
        &mut env,
        "resultImplicitCaller",
        "def resultImplicitCaller : Nat := @resultImplicit (Nat -> Nat) 2 (fun (x : Nat) => x)",
    );
    assert_application(&env, "resultImplicitCaller", &[], 0);
}

/// Lean-faithful refusal (decision D2, 2026-10-02, `docs/DECISIONS.md`:
/// Clean never accepts what Lean rejects). Every arm here re-binds the result
/// type's implicit (`fun {A : Type} (x : A) => …`), and pinned lean
/// v4.30.0-rc2 REJECTS that spelling, because Lean introduces `{A}` once as an
/// implicit lambda around the whole `match` and each arm then faces `A✝ → Nat`:
///
/// ```text
/// error: Type mismatch
///   fun {A} x => acc
/// has type
///   {A : Type} → A → Nat
/// of sort `Type 1` but is expected to have type
///   A✝ → Nat
/// ```
///
/// bb3b6ffe6 accepted it on purpose, as a pinned superset of Lean; D2 retired
/// that superset. The Lean-valid spelling of the same subject is
/// `recursive_function_results_insert_implicit_binders_lean_spelling` below,
/// and it must keep elaborating.
#[test]
fn recursive_function_results_insert_their_own_implicit_binders() {
    let mut env = nat_environment();
    let decl = parse_decl(
        r"def resultBinderPrefix (acc : Nat) (n : Nat) : {A : Type} -> A -> Nat := match n with
| Nat.zero => fun {A : Type} (x : A) => acc
| Nat.succ k => fun {A : Type} (x : A) => resultBinderPrefix (Nat.succ acc) k x",
    )
    .expect("the Lean-rejected spelling is syntactically valid");
    let result = elaborate_decl_and_register(&mut env, &decl);
    assert!(
        result.is_err(),
        "pinned Lean refuses an arm that re-binds the result type's implicit; Clean must too (D2)"
    );
    assert!(
        env.get_const(&Name::from_string("resultBinderPrefix"))
            .is_none(),
        "a refused definition must not be registered"
    );
}

/// The same subject in the spelling pinned Lean ACCEPTS: the arms bind only
/// `x`, Lean has already introduced `{A}` around the `match`, and the
/// recursive call must insert its own `{A}`. Pinned lean v4.30.0-rc2 accepts
/// it and `#eval resultBinderLeanCaller` prints 5.
#[test]
fn recursive_function_results_insert_implicit_binders_lean_spelling() {
    let mut env = nat_environment();
    register(
        &mut env,
        "resultBinderLean",
        r"def resultBinderLean (acc : Nat) (n : Nat) : {A : Type} -> A -> Nat := match n with
| Nat.zero => fun x => acc
| Nat.succ k => fun x => resultBinderLean (Nat.succ acc) k x",
    );
    register(
        &mut env,
        "resultBinderLeanCaller",
        "def resultBinderLeanCaller : Nat := resultBinderLean 3 2 (7 : Nat)",
    );
    assert_application(&env, "resultBinderLeanCaller", &[], 5);
}

#[test]
fn ill_typed_changed_prefix_parameter_is_rejected() {
    let mut env = nat_environment();
    let decl = parse_decl(
        r"def badPrefix (acc : Nat) (n : Nat) : Nat := match n with
| Nat.zero => acc
| Nat.succ k => badPrefix (fun (x : Nat) => x) k",
    )
    .expect("the deliberately ill-typed source is syntactically valid");
    let result = elaborate_decl_and_register(&mut env, &decl);
    if result.is_ok() {
        // Pin the actual failure mode: accepting an unrelated, well-typed
        // constant-accumulator body does not validate the submitted source.
        recheck_stored_definition(&env, "badPrefix");
        panic!("an ill-typed Nat prefix was erased into a kernel-valid definition");
    }
    assert!(
        env.get_const(&Name::from_string("badPrefix")).is_none(),
        "a refused definition must not be registered"
    );
}

#[test]
fn unchanged_prefix_parameter_keeps_its_value() {
    let mut env = nat_environment();
    register(
        &mut env,
        "fixedPrefix",
        r"def fixedPrefix (acc : Nat) (n : Nat) : Nat := match n with
| Nat.zero => acc
| Nat.succ k => fixedPrefix acc k",
    );
    assert_application(&env, "fixedPrefix", &[5, 2], 5);
}

#[test]
fn changed_trailing_parameter_keeps_existing_support() {
    let mut env = nat_environment();
    register(
        &mut env,
        "trailingAccum",
        r"def trailingAccum (n : Nat) (acc : Nat) : Nat := match n with
| Nat.zero => acc
| Nat.succ k => trailingAccum k (Nat.succ acc)",
    );
    assert_application(&env, "trailingAccum", &[2, 0], 2);
    assert_application(&env, "trailingAccum", &[2, 3], 5);
}

#[test]
fn uniform_constructor_parameters_are_not_explicit_application_arguments() {
    let mut list = prefix_list_environment();
    reject(
        &mut list,
        "badListParameter",
        "def badListParameter : PrefixList Nat := PrefixList.nil Nat",
    );
    let mut vector = prefix_vec_environment();
    reject(
        &mut vector,
        "badVecParameter",
        "def badVecParameter : PrefixVec Nat 0 := PrefixVec.nil Nat",
    );
}
