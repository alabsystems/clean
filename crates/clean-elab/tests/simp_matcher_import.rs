// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Imported matchers reduce by their recorded identity and actual definition.
//! These statements unfold the authored function, never its generated helper.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::{Environment, Name, TypeChecker};

#[test]
fn imported_matchers_select_only_the_actual_constructor_branch() {
    std::thread::Builder::new().stack_size(128 << 20).spawn(|| {
        let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/olean/v4.8.0/matcher-metadata");
        let core = clean_olean::installed_lean_lib_path("leanprover/lean4:v4.8.0")
            .expect("the exact Lean 4.8 library is required for this imported fixture");
        let mut imported = Environment::default();
        clean_olean::load_module_with_deps(&mut imported, "MatcherParity", &[fixture, core]).unwrap();
        let hidden = "def hidden : MatcherParity.Box := MatcherParity.Box.wrap MatcherParity.Flag.off";
        for decl in clean_parser::parse_file(hidden).unwrap() {
            let mut context = FileContext::new();
            let decl = preprocess_decl_with_context(&decl, &mut context);
            elaborate_decl_and_register_with_context(&mut imported, &decl, &mut context).unwrap();
        }
        let positives = [
            ("MatcherParity.Box.empty", "x"),
            ("MatcherParity.Box.wrap MatcherParity.Flag.off", "y"),
            ("MatcherParity.Box.wrap MatcherParity.Flag.on", "z"),
        ];
        for (constructor, result) in positives {
            let mut env = imported.clone();
            let source = format!("theorem checked (x y z : Nat) : MatcherParity.choose ({constructor}) x y z = {result} := by simp only [MatcherParity.choose]");
            let mut context = FileContext::new();
            for decl in clean_parser::parse_file(&source).unwrap() {
                let decl = preprocess_decl_with_context(&decl, &mut context);
                elaborate_decl_and_register_with_context(&mut env, &decl, &mut context).unwrap();
            }
            let name = Name::from_string("checked");
            let declaration = env.get_const(&name).unwrap();
            TypeChecker::new(&env).check_type(declaration.value.as_ref().unwrap(), &declaration.type_).unwrap();
            assert!(env.axiom_deps(&name).unwrap().is_empty());
        }
        for (function, arguments, result) in [
            // The final reflexivity check may unfold a semireducible definition
            // even though the matcher-selection fast path does not unfold it.
            ("choose", "hidden x y z", "y"),
            ("chooseEq", "(MatcherParity.Box.wrap MatcherParity.Flag.off) x y z", "y"),
            ("chooseTwo", "MatcherParity.Flag.off MatcherParity.Flag.off x y z w", "x"),
            ("chooseTwo", "MatcherParity.Flag.off MatcherParity.Flag.on x y z w", "y"),
            ("chooseTwo", "MatcherParity.Flag.on MatcherParity.Flag.off x y z w", "z"),
            ("chooseTwo", "MatcherParity.Flag.on MatcherParity.Flag.on x y z w", "w"),
        ] {
            let mut env = imported.clone();
            let extra = if arguments.starts_with("hidden") { ", hidden" } else { "" };
            let source = format!("theorem checked (x y z w : Nat) : MatcherParity.{function} {arguments} = {result} := by simp only [MatcherParity.{function}{extra}]");
            let mut context = FileContext::new();
            for decl in clean_parser::parse_file(&source).unwrap() {
                let decl = preprocess_decl_with_context(&decl, &mut context);
                elaborate_decl_and_register_with_context(&mut env, &decl, &mut context).unwrap();
            }
            let name = Name::from_string("checked");
            let declaration = env.get_const(&name).unwrap();
            TypeChecker::new(&env).check_type(declaration.value.as_ref().unwrap(), &declaration.type_).unwrap();
            assert!(env.axiom_deps(&name).unwrap().is_empty());
        }
        for source in [
            "theorem rejected (x y z : Nat) : MatcherParity.choose hidden x y z = y := by simp only [MatcherParity.choose]",
            "theorem rejected (x y z : Nat) : MatcherParity.choose (MatcherParity.Box.wrap MatcherParity.Flag.off) x y z = z := by simp only [MatcherParity.choose]",
            "theorem rejected (b : MatcherParity.Box) (x y z : Nat) : MatcherParity.choose b x y z = y := by simp only [MatcherParity.choose]",
            "theorem rejected (x y z : Nat) : (fun b => MatcherParity.choose b x y z) = (fun b => y) := by simp only [MatcherParity.choose]",
        ] {
            let mut env = imported.clone();
            let mut context = FileContext::new();
            let decl = clean_parser::parse_file(source).unwrap().pop().unwrap();
            let decl = preprocess_decl_with_context(&decl, &mut context);
            let error = elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
                .expect_err("a wrong or unknown constructor must not select this branch");
            assert!(matches!(error.innermost(), clean_elab::ElabError::TacticFailed(
                clean_elab::tactic::TacticError::UnsolvedGoals { .. }
                | clean_elab::tactic::TacticError::NoProgress { .. }
            )), "unexpected refusal: {error}");
            assert!(env.get_const(&Name::from_string("rejected")).is_none());
        }
    }).unwrap().join().unwrap();
}
