// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Import actual Lean course-of-values definitions and use their checked equations.
use clean_elab::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Expr, ExprKind, Name, TypeChecker};
use std::path::Path;
use std::process::Command;

const MODULE: &str = include_str!("fixtures/imported_equations/ImportedEquations.lean");
const CASES_ON: &str = include_str!("fixtures/imported_equations/cases_on.lean");
const POSITIVE: &str = include_str!("fixtures/imported_equations/positive.lean");

fn elaborate(env: &mut Environment, source: &str) -> Result<(), String> {
    let mut context = FileContext::new();
    for decl in clean_parser::parse_file(source).map_err(|e| e.to_string())? {
        // The environment has already loaded this real module, using the same loader.
        if matches!(decl, clean_parser::SurfaceDecl::Import { .. }) {
            continue;
        }
        let decl = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register_with_context(env, &decl, &mut context)
            .map_err(|e| e.to_string())?;
        fn error(result: &ElabResult) -> Option<String> {
            match result {
                ElabResult::Failed { error, .. } => Some(error.to_string()),
                ElabResult::Multiple(results) => results.iter().find_map(error),
                _ => None,
            }
        }
        if let Some(error) = error(&result) {
            return Err(error);
        }
    }
    Ok(())
}

fn oracle(dir: &Path, file: &str, source: &str, compile: bool) -> std::process::Output {
    std::fs::write(dir.join(file), source).expect("write oracle source");
    let mut command = Command::new(clean_olean::pinned_lean_binary().expect("pinned Lean"));
    command.current_dir(dir).env("LEAN_PATH", dir);
    if compile {
        command.args(["-o", "ImportedEquations.olean"]);
    }
    command.arg(file).output().expect("run pinned Lean")
}

fn mentions_brec_on(expr: &Expr) -> bool {
    match expr.kind() {
        ExprKind::Const(name, _) => name.to_string().ends_with(".brecOn"),
        ExprKind::App(f, a) => mentions_brec_on(f) || mentions_brec_on(a),
        ExprKind::Lam(_, a, b) | ExprKind::Pi(_, a, b) => {
            mentions_brec_on(a) || mentions_brec_on(b)
        }
        ExprKind::Let(_, ty, value, body, _) => {
            mentions_brec_on(ty) || mentions_brec_on(value) || mentions_brec_on(body)
        }
        ExprKind::MData(_, e) | ExprKind::Proj(_, _, e) => mentions_brec_on(e),
        _ => false,
    }
}

#[test]
fn imported_course_of_values_equations_are_used_and_checked() {
    std::thread::Builder::new().stack_size(128 << 20).spawn(|| {
        let dir = tempfile::tempdir().expect("fixture directory");
        let compiled = oracle(dir.path(), "ImportedEquations.lean", MODULE, true);
        assert!(compiled.status.success(), "{}", String::from_utf8_lossy(&compiled.stdout));
        eprintln!("fixture compiled; loading its explicit Init.SimpLemmas dependency closure");
        let mut env = Environment::default();
        clean_olean::declare_environment_world(&mut env, "v4.30.0-rc2").expect("fixture world");
        let core = clean_olean::installed_lean_lib_path("leanprover/lean4:v4.30.0-rc2").expect("pinned library");
        clean_olean::load_module_with_deps(&mut env, "ImportedEquations", &[dir.path().to_path_buf(), core]).expect("import real equations");
        eprintln!("dependency closure loaded: {} constants", env.num_constants());
        let function = env.get_const(&Name::from_string("ImportedEquations.good")).expect("function");
        assert!(mentions_brec_on(function.value.as_ref().expect("body")), "fixture must exercise imported brecOn");
        for index in [1, 2] {
            let name = Name::from_string(&format!("ImportedEquations.good.eq_{index}"));
            let equation = env.get_const(&name).expect("realized equation imported");
            assert!(matches!(equation.kind, clean_kernel::env::ConstantKind::Theorem));
            assert!(equation.value.is_some(), "equation has an actual proof");
        }
        let independent = oracle(dir.path(), "Positive.lean", POSITIVE, false);
        assert!(independent.status.success(), "{}", String::from_utf8_lossy(&independent.stdout));
        let mut checked = env.clone();
        elaborate(&mut checked, POSITIVE).expect("imported equation proofs");
        for text in ["explicit_equations", "registered_equations", "readd_equations"] {
            let name = Name::from_string(text);
            let decl = checked.get_const(&name).expect("checked theorem");
            TypeChecker::new(&checked).check_type(decl.value.as_ref().expect("proof"), &decl.type_).expect("kernel recheck");
            let dependencies = checked.axiom_deps(&name).expect("axiom closure");
            assert!(dependencies.iter().all(|axiom| checked.is_canonical_foundational_axiom(axiom)), "{name}: {dependencies:?}");
        }
        let cases_on = env.get_const(&Name::from_string("ImportedEquations.Tree.casesOn")).expect("imported casesOn");
        assert!(matches!(cases_on.kind, clean_kernel::env::ConstantKind::Definition));
        assert!(env.get_recursor(&Name::from_string("ImportedEquations.Tree.casesOn")).is_none());
        assert!(oracle(dir.path(), "CasesOn.lean", CASES_ON, false).status.success());
        let mut cases_checked = env.clone();
        elaborate(&mut cases_checked, CASES_ON).expect("imported casesOn selects constructor before simplifying branches");
        for text in ["checkGuard", "forkGuard"] {
            let name = Name::from_string(text);
            let decl = cases_checked.get_const(&name).expect("checked casesOn theorem");
            TypeChecker::new(&cases_checked).check_type(decl.value.as_ref().expect("proof"), &decl.type_).expect("casesOn kernel recheck");
            let dependencies = cases_checked.axiom_deps(&name).expect("casesOn axiom closure");
            assert!(dependencies.iter().all(|axiom| cases_checked.is_canonical_foundational_axiom(axiom)), "{name}: {dependencies:?}");
        }
        for source in [
            "theorem unknownMajor (p : β → Prop) (f : α → Option β) (e : Tree α) : Guard p f e := by simp only [Guard]",
            "theorem missingPremise (p : β → Prop) (f : α → Option β) (a : α) (d : β) (h : f a = some d) : Guard p f (.leaf a) := by simp_all only [Guard]",
        ] {
            let combined = format!("{CASES_ON}\n{source}");
            assert!(!oracle(dir.path(), "CasesNegative.lean", &combined, false).status.success());
            let mut rejected = cases_checked.clone();
            let error = elaborate(&mut rejected, &format!("open ImportedEquations\n{source}")).expect_err("unknown major or missing leaf premise must fail");
            assert!(error.contains("unsolved") || error.contains("progress"), "{error}");
        }
        for source in [
            "import ImportedEquations\nopen ImportedEquations\ntheorem bad {α : Type u} (a b : Tree α) (ha : good a) : good (.fork a b) := by simp only [good, ha]",
            "import ImportedEquations\nopen ImportedEquations\ntheorem bad {α : Type u} (a b : Tree α) (ha : good a) (hb : good b) : good (.fork a b) := by simp only [good, -good.eq_2, ha, hb]",
        ] {
            assert!(!oracle(dir.path(), "Negative.lean", source, false).status.success());
            let mut rejected = env.clone();
            let error = elaborate(&mut rejected, source).expect_err("missing premise or disabled equation must fail");
            assert!(error.contains("unsolved") || error.contains("progress"), "{error}");
            assert!(rejected.get_const(&Name::from_string("bad")).is_none());
        }
    }).expect("test thread").join().expect("imported-equations test");
}

#[test]
fn imported_brec_on_reduces_without_pre_realized_equations() {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(|| {
            let dir = tempfile::tempdir().expect("lazy equation fixture");
            let module = r"prelude
import Init.SimpLemmas
namespace ImportedEquations
inductive Tree (α : Type u) where
  | leaf : α → Tree α
  | fork : Tree α → Tree α → Tree α
def good : Tree α → Prop
  | .leaf _ => True
  | .fork a b => good a ∧ good b
def depthGood (depth : Nat) : Tree α → Prop
  | .leaf _ => depth = 0
  | .fork a b => depthGood depth a ∧ depthGood (depth + 1) b
end ImportedEquations
";
            let compiled = oracle(dir.path(), "ImportedEquations.lean", module, true);
            assert!(compiled.status.success(), "{}", String::from_utf8_lossy(&compiled.stdout));
            let mut env = Environment::default();
            clean_olean::declare_environment_world(&mut env, "v4.30.0-rc2").expect("world");
            let core = clean_olean::installed_lean_lib_path("leanprover/lean4:v4.30.0-rc2").expect("library");
            clean_olean::load_module_with_deps(&mut env, "ImportedEquations", &[dir.path().to_path_buf(), core]).expect("load fixture");
            for definition in ["good", "depthGood"] {
                let name = Name::from_string(&format!("ImportedEquations.{definition}"));
                assert!(mentions_brec_on(env.get_const(&name).expect("definition").value.as_ref().expect("value")));
                assert!(env.get_const(&name.str("eq_1")).is_none(), "fixture must not pre-realize equations");
            }
            for (name, proof) in [
                ("explicit", "theorem explicit {α : Type u} (a b : Tree α) (ha : good a) (hb : good b) : good (.fork a b) := by simp only [good, ha, hb, and_self]"),
                ("all", "theorem all {α : Type u} (a b : Tree α) (ha : good a) (hb : good b) : good (.fork a b) := by simp_all only [good, and_self]"),
                ("depth", "theorem depth {α : Type u} (a b : Tree α) (n : Nat) (ha : depthGood n a) (hb : depthGood (n + 1) b) : depthGood n (.fork a b) := by simp_all only [depthGood, and_self]"),
            ] {
                let source = format!("import ImportedEquations\nopen ImportedEquations\n{proof}\n");
                let accepted = oracle(dir.path(), "Positive.lean", &source, false);
                assert!(accepted.status.success(), "{name}: {}", String::from_utf8_lossy(&accepted.stdout));
                let mut checked = env.clone();
                elaborate(&mut checked, &source).unwrap_or_else(|error| panic!("{name}: {error}"));
                let name = Name::from_string(name);
                let theorem = checked.get_const(&name).expect("theorem");
                TypeChecker::new(&checked).check_type(theorem.value.as_ref().expect("proof"), &theorem.type_).expect("kernel recheck");
                assert!(checked.axiom_deps(&name).expect("closure").iter().all(|a| checked.is_canonical_foundational_axiom(a)));
            }
            for proof in [
                "theorem bad {α : Type u} (a b : Tree α) (ha : good a) : good (.fork a b) := by simp_all only [good, and_self]",
                "theorem bad {α : Type u} (a b : Tree α) (n : Nat) (ha : depthGood n a) (hb : depthGood n b) : depthGood n (.fork a b) := by simp_all only [depthGood, and_self]",
            ] {
                let source = format!("import ImportedEquations\nopen ImportedEquations\n{proof}\n");
                assert!(!oracle(dir.path(), "Negative.lean", &source, false).status.success());
                assert!(elaborate(&mut env.clone(), &source).is_err());
            }
        })
        .expect("test thread")
        .join()
        .expect("lazy equations test");
}
