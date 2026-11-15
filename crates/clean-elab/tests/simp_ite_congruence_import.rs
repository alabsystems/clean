// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary ite congruence must work under simp only, independently of
//! reduceIte. These claims use genuine Lean 4.8 declarations: its Init has
//! ite_congr and congrFun, but no builtin-only congrFun'. The negative rows
//! also pin the distinction between transporting a condition and selecting
//! a branch. No imported declaration or axiom is fabricated by this test.

use clean_elab::tactic::TacticError;
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabError, FileContext,
};
use clean_kernel::{Environment, Name, TypeChecker};
use clean_parser::parse_file;

fn register(env: &mut Environment, source: &str) -> Result<(), ElabError> {
    let mut context = FileContext::new();
    for decl in parse_file(source).expect("static regression input parses") {
        let processed = preprocess_decl_with_context(&decl, &mut context);
        elaborate_decl_and_register_with_context(env, &processed, &mut context)?;
    }
    Ok(())
}

#[test]
fn imported_ite_condition_congruence_preserves_proofs_and_simp_only_scope() {
    std::thread::Builder::new().stack_size(64 << 20).spawn(|| {
        let lib = clean_olean::installed_lean_lib_path("leanprover/lean4:v4.8.0")
            .expect("this regression requires the exact installed Lean 4.8.0 standard library");
        let mut imported = Environment::default();
        imported.ensure_native_reducers();
        clean_olean::load_module_with_deps(&mut imported, "Init.Data.Bool", &[lib])
            .expect("original Lean 4.8 Bool/SimpLemmas declarations must load");
        for name in ["ite_congr", "congrFun", "ite_false", "ite_true"] {
            assert!(imported.get_const(&Name::from_string(name)).is_some(), "missing {name}");
        }
        assert!(imported.get_const(&Name::from_string("congrFun'")).is_none());
        let positives = [
            "theorem checked (b : Bool) (h : b = false) (x y : Nat) : (if b then x else y) = y := by simp only [h, Bool.false_eq_true, ite_false]",
            "theorem checked (b : Bool) (h : b = true) (x y : Nat) : (if b then x else y) = x := by simp only [h, ite_true]",
            "theorem checked (p q : Prop) [Decidable p] [Decidable q] (h : p = q) (x y : Nat) : (if p then x else y) = (if q then x else y) := by simp only [h]",
            "theorem checked (x y : Nat) : (if False then x else y) = y := by simp only [ite_false]",
        ];
        for source in positives {
            let mut env = imported.clone();
            register(&mut env, source).unwrap_or_else(|e| panic!("{source}: {e}"));
            let name = Name::from_string("checked");
            let decl = env.get_const(&name).expect("the claim is registered");
            TypeChecker::new(&env).check_type(decl.value.as_ref().expect("proof body"), &decl.type_)
                .expect("the produced proof checks against its original claim");
            assert!(env.axiom_deps(&name).expect("tracked proof dependencies").is_empty());
        }
        let negatives = [
            "theorem rejected (b : Bool) (h : b = false) (x y : Nat) : (if b then x else y) = y := by simp only [h]",
            "theorem rejected (b : Bool) (h : b = false) (x y : Nat) : (if b then x else y) = y := by simp only [h, Bool.false_eq_true]",
            "theorem rejected (p : Prop) [Decidable p] (h : p = False) (x y : Nat) : (if p then x else y) = y := by simp only [h]",
            "theorem rejected (p : Prop) [Decidable p] (h : p = True) (x y : Nat) : (if p then x else y) = x := by simp only [h]",
            "theorem rejected (x y : Nat) : (if False then x else y) = y := by simp only []",
            "theorem rejected (b : Bool) (h : b = false) : (if b then Nat.zero else Nat.succ Nat.zero) = Nat.zero := by simp only [h, Bool.false_eq_true, ite_false]",
            "theorem rejected (b : Bool) (h : b = true) : (if b then Nat.zero else Nat.succ Nat.zero) = Nat.succ Nat.zero := by simp only [h, ite_true]",
        ];
        for source in negatives {
            let mut env = imported.clone();
            let error = register(&mut env, source).expect_err("the original claim must stay unproved");
            assert!(matches!(error.innermost(), ElabError::TacticFailed(TacticError::UnsolvedGoals { .. } | TacticError::NoProgress { .. })), "unexpected refusal: {error}");
            assert!(env.get_const(&Name::from_string("rejected")).is_none());
        }
    }).unwrap().join().unwrap();
}
