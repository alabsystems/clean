// Copyright 2026 Andrew Yates. SPDX-License-Identifier: Apache-2.0

//! Original source-defined predicate and application from the W1 source replay.

use super::super::{synthesize_native_equations, SimpLemma};
use crate::{
    elaborate_decl_and_register_with_context, preprocess_decl_with_context, ElabResult, FileContext,
};
use clean_kernel::{Environment, Expr, ExprKind, Level, Name, TypeChecker};
use std::path::Path;
use std::process::{Command, Output};

const ORIGINAL: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../reports/self-proof-w1-sort-bound-rewrite-2026-11-19/Application.lean"
));

fn require_success(output: Output) {
    assert!(
        output.status.success(),
        "pinned Lean failed:\n{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
}

fn import_source_dependencies(artifacts: &Path, lean: &Path) -> Environment {
    let package = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../theories/cic_l");
    std::fs::create_dir(artifacts.join("CICL")).expect("output directory");
    for module in ["Level", "ListSupport", "Expr", "Declaration"] {
        require_success(
            Command::new(lean)
                .current_dir(&package)
                .env("LEAN_PATH", artifacts)
                .args(["-o"])
                .arg(artifacts.join(format!("CICL/{module}.olean")))
                .arg(format!("CICL/{module}.lean"))
                .output()
                .expect("compile source import"),
        );
    }
    let mut env = Environment::default();
    clean_olean::declare_environment_world(&mut env, "v4.30.0-rc2").expect("checker world");
    let paths = [
        artifacts.to_path_buf(),
        clean_olean::pinned_lean_lib_path().expect("pinned SDK library"),
    ];
    let modules = ["Init", "CICL.Declaration", "CICL.ListSupport"].map(str::to_string);
    clean_olean::load_modules_with_deps(&mut env, &modules, &paths)
        .expect("load the genuine imports");
    env
}

fn elaborate(env: &mut Environment, source: &str) -> Result<(), String> {
    fn failure(result: &ElabResult) -> Option<String> {
        match result {
            ElabResult::Failed { error, .. } => Some(error.to_string()),
            ElabResult::Multiple(results) => results.iter().find_map(failure),
            _ => None,
        }
    }
    let mut context = FileContext::new();
    for decl in clean_parser::parse_file(source).expect("source parses") {
        if matches!(decl, clean_parser::SurfaceDecl::Import { .. }) {
            continue;
        }
        let decl = preprocess_decl_with_context(&decl, &mut context);
        let result = elaborate_decl_and_register_with_context(env, &decl, &mut context)
            .map_err(|e| e.to_string())?;
        if let Some(error) = failure(&result) {
            return Err(error);
        }
    }
    Ok(())
}

/// The reported equation has loose variables over the predicate's two fixed
/// parameters and this constructor's fields. Close its actual template at
/// those types before checking it against both the synthesized and altered RHS.
fn check_equation(env: &Environment, predicate: &Name, equation: &SimpLemma) {
    let mut bindings = Vec::new();
    let mut ty = &env.get_const(predicate).expect("source predicate").type_;
    for _ in 0..2 {
        let ExprKind::Pi(info, domain, next) = ty.kind() else {
            panic!("fixed parameter");
        };
        bindings.push((*info, domain.as_ref().clone()));
        ty = next;
    }
    let args = equation.lhs.get_app_args();
    let ctor = args.last().expect("major").get_app_fn();
    let ExprKind::Const(name, _) = ctor.kind() else {
        panic!("source constructor");
    };
    let mut ty = &env.get_const(name).expect("constructor type").type_;
    while let ExprKind::Pi(info, domain, next) = ty.kind() {
        bindings.push((*info, domain.as_ref().clone()));
        ty = next;
    }
    let eq = Expr::const_(Name::from_string("Eq"), vec![Level::succ(Level::zero())]);
    let statement = |rhs| Expr::apps(eq.clone(), [Expr::prop(), equation.lhs.clone(), rhs]);
    assert_eq!(equation.eq_type.as_ref(), Some(&Expr::prop()));
    let mut correct = statement(equation.rhs.clone());
    let mut wrong = statement(Expr::const_(Name::from_string("False"), vec![]));
    let mut proof = equation
        .proof_expr
        .clone()
        .expect("generated proof template");
    for (info, domain) in bindings.into_iter().rev() {
        proof = Expr::lam(info, domain.clone(), proof);
        correct = Expr::pi(info, domain.clone(), correct);
        wrong = Expr::pi(info, domain, wrong);
    }
    let kernel = TypeChecker::new(env);
    kernel
        .check_type(&proof, &correct)
        .unwrap_or_else(|e| panic!("{name}: {e}"));
    assert!(
        kernel.check_type(&proof, &wrong).is_err(),
        "{name}: replaced the RHS with False"
    );
}

#[test]
fn source_predicate_checks_each_generated_equation_and_the_original_application() {
    std::thread::Builder::new()
        .stack_size(128 << 20)
        .spawn(|| {
            let temp = tempfile::tempdir().expect("fixture directory");
            let artifacts = temp.path();
            let lean = clean_olean::pinned_lean_binary().expect("pinned Lean");
            let base = import_source_dependencies(artifacts, &lean);
            let wrong = ORIGINAL.replace("h_a, h_D]", "h_a, h_f]");
            assert_ne!(wrong, ORIGINAL, "wrong-child control changed no text");
            for (file, source) in [("Original.lean", ORIGINAL), ("WrongChild.lean", &wrong)] {
                std::fs::write(artifacts.join(file), source).unwrap();
                let reference = Command::new(&lean)
                    .current_dir(artifacts)
                    .env("LEAN_PATH", artifacts)
                    .arg(file)
                    .output()
                    .expect("run pinned Lean");
                let mut env = base.clone();
                let result = elaborate(&mut env, source);
                if file == "WrongChild.lean" {
                    assert!(!reference.status.success());
                    assert!(String::from_utf8_lossy(&reference.stdout).contains("unsolved goals"));
                    assert!(result
                        .expect_err("the domain hypothesis was omitted")
                        .contains("unsolved goal"));
                    continue;
                }
                require_success(reference);
                result.expect("original source predicate application");
                let theorem = env
                    .get_const(&Name::from_string("KCheckSpec.check_app"))
                    .expect("theorem");
                TypeChecker::new(&env)
                    .check_type(theorem.value.as_ref().expect("proof"), &theorem.type_)
                    .expect("original application proof must kernel check");
                let predicate = Name::from_string("KCheckSpec.Term.SortsWithin");
                let equations =
                    synthesize_native_equations(&env, &predicate).expect("source equations");
                assert_eq!(equations.len(), 9);
                for equation in &equations {
                    check_equation(&env, &predicate, equation);
                }
            }
        })
        .expect("qualified stack")
        .join()
        .expect("source predicate test");
}

#[test]
fn equation_carrier_universe_agrees_with_kernel_for_sorts() {
    let env = Environment::new();
    let kernel = TypeChecker::new(&env);
    let parameter = Name::from_string("u");
    for level in [
        Level::zero(),
        Level::succ(Level::zero()),
        Level::param(parameter.clone()),
    ] {
        let carrier = Expr::sort(level);
        let actual = super::super::sort_level_of_result_type(
            &env,
            &carrier,
            std::slice::from_ref(&parameter),
        )
        .expect("a sort is a supported equation carrier");
        assert_eq!(
            Expr::sort(actual),
            kernel.infer_type(&carrier).expect("kernel sort type")
        );
    }
}
