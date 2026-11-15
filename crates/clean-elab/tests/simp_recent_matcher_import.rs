// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recent native matcher metadata must reach ordinary imported simplification.

use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, FileContext,
};
use clean_kernel::{Environment, Name, TypeChecker};

fn check_recent_matchers(version: &'static str) {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(move || {
            let fixture = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
                .join(format!("../../tests/fixtures/olean/{version}/matcher-metadata"));
            let core = clean_olean::installed_lean_lib_path(&format!("leanprover/lean4:{version}"))
                .expect("the exact official library is required for this recent matcher fixture");
            let mut imported = Environment::default();
            clean_olean::declare_environment_world(&mut imported, version).unwrap();
            clean_olean::load_module_with_deps(&mut imported, "MatcherParity", &[fixture, core])
                .unwrap();
            for suffix in ["choose", "chooseEq", "chooseTwo", "chooseOverlap"] {
                let name = Name::from_string(&format!("MatcherParity.{suffix}.match_1"));
                assert!(imported.get_matcher_info(&name).unwrap().details.is_some());
            }
            assert!(imported
                .get_matcher_info(&Name::from_string("MatcherParity.ordinary.match_1"))
                .is_none());
            for (function, arguments, result) in [
                ("choose", "MatcherParity.Box.empty x y z", "x"),
                ("choose", "(MatcherParity.Box.wrap MatcherParity.Flag.off) x y z", "y"),
                ("choose", "(MatcherParity.Box.wrap MatcherParity.Flag.on) x y z", "z"),
                ("chooseEq", "(MatcherParity.Box.wrap MatcherParity.Flag.off) x y z", "y"),
                ("chooseTwo", "MatcherParity.Flag.off MatcherParity.Flag.off x y z w", "x"),
                ("chooseTwo", "MatcherParity.Flag.off MatcherParity.Flag.on x y z w", "y"),
                ("chooseTwo", "MatcherParity.Flag.on MatcherParity.Flag.off x y z w", "z"),
                ("chooseTwo", "MatcherParity.Flag.on MatcherParity.Flag.on x y z w", "w"),
                ("chooseOverlap", "MatcherParity.Flag.off MatcherParity.Flag.on", "1"),
                ("chooseOverlap", "MatcherParity.Flag.on MatcherParity.Flag.off", "2"),
                ("chooseOverlap", "MatcherParity.Flag.on MatcherParity.Flag.on", "3"),
            ] {
                let mut env = imported.clone();
                let source = format!("theorem checked (x y z w : Nat) : MatcherParity.{function} {arguments} = {result} := by simp only [MatcherParity.{function}]");
                let mut context = FileContext::new();
                for decl in clean_parser::parse_file(&source).unwrap() {
                    let decl = preprocess_decl_with_context(&decl, &mut context);
                    elaborate_decl_and_register_with_context(&mut env, &decl, &mut context).unwrap();
                }
                let name = Name::from_string("checked");
                let declaration = env.get_const(&name).unwrap();
                TypeChecker::new(&env)
                    .check_type(declaration.value.as_ref().unwrap(), &declaration.type_)
                    .unwrap();
                assert!(env.axiom_deps(&name).unwrap().is_empty());
            }
            for source in [
                "theorem rejected (x y z : Nat) : MatcherParity.choose (MatcherParity.Box.wrap MatcherParity.Flag.off) x y z = z := by simp only [MatcherParity.choose]",
                "theorem rejected (b : MatcherParity.Box) (x y z : Nat) : MatcherParity.choose b x y z = y := by simp only [MatcherParity.choose]",
                "theorem rejected : MatcherParity.chooseOverlap MatcherParity.Flag.off MatcherParity.Flag.on = 3 := by simp only [MatcherParity.chooseOverlap]",
            ] {
                let mut env = imported.clone();
                let mut context = FileContext::new();
                let decl = clean_parser::parse_file(source).unwrap().pop().unwrap();
                let decl = preprocess_decl_with_context(&decl, &mut context);
                let error = elaborate_decl_and_register_with_context(&mut env, &decl, &mut context)
                    .expect_err("wrong branches and unknown discriminants must not close");
                assert!(matches!(error.innermost(), clean_elab::ElabError::TacticFailed(
                    clean_elab::tactic::TacticError::UnsolvedGoals { .. }
                    | clean_elab::tactic::TacticError::NoProgress { .. }
                    | clean_elab::tactic::TacticError::TypeMismatch { .. }
                )), "unexpected refusal: {error}");
                assert!(env.get_const(&Name::from_string("rejected")).is_none());
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn recent_matchers_435_preserve_imported_branch_selection_and_proofs() {
    check_recent_matchers("v4.35.0");
}

#[test]
fn recent_matchers_436rc2_preserve_imported_branch_selection_and_proofs() {
    check_recent_matchers("v4.36.0-rc2");
}
