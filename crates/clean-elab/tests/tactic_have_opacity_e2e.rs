// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact sources measured on genuine Lean 4.30, 4.35 and 4.36-rc2.
//! Marked have proofs stay opaque; genuine local definitions reduce.

use clean_elab::tactic::builtins::builtin_tactic_patterns;
use clean_elab::tactic::{TacticGoalCapture, TacticGoalObservationKind};
use clean_elab::{
    elaborate_decl_and_register, elaborate_decl_and_register_with_context,
    preprocess_decl_with_context, FileContext,
};
use clean_kernel::env::Environment;
use clean_kernel::{Expr, ExprKind, MDataValue, Name, TypeChecker};
use clean_parser::parse_file_with_tactics;

fn check_case(source: &str, name: &str, accepts: bool) {
    let mut env = Environment::with_prelude();
    let mut context = FileContext::new();
    let declarations = parse_file_with_tactics(source, &builtin_tactic_patterns())
        .expect("the measured source must parse");
    let result = declarations.iter().try_for_each(|declaration| {
        let declaration = preprocess_decl_with_context(declaration, &mut context);
        elaborate_decl_and_register(&mut env, &declaration).map(|_| ())
    });
    let name = Name::from_string(name);
    if !accepts {
        assert!(result.is_err(), "the wrong proof must be rejected");
        assert!(
            env.get_const(&name).is_none(),
            "a rejected theorem must not register"
        );
        return;
    }
    result.expect("the native-accepted source must elaborate and kernel-check");
    let info = env.get_const(&name).expect("the theorem must register");
    let proof = info
        .value
        .as_ref()
        .expect("the theorem must contain a proof");
    assert!(!proof.has_fvar_quick(), "registered proofs must be closed");
    let checker = TypeChecker::new(&env);
    let inferred = checker.infer_type(proof).expect("the proof must infer");
    assert!(checker.is_def_eq(&inferred, &info.type_));
    assert!(env
        .axiom_deps(&name)
        .expect("axiom closure must exist")
        .is_empty());
}

macro_rules! measured_case {
    ($case:ident, $name:literal, $accepts:literal) => {
        #[test]
        fn $case() {
            check_case(
                include_str!(concat!(
                    "fixtures/have_opacity/",
                    stringify!($case),
                    ".lean"
                )),
                $name,
                $accepts,
            );
        }
    };
}

measured_case!(have_bad, "opaque_refl_have_bad", false);
measured_case!(have_self_ok, "opaque_refl_have_self_ok", true);
measured_case!(let_ok, "opaque_refl_let_ok", true);
measured_case!(let_bad, "opaque_refl_let_bad", false);
measured_case!(have_term_bad, "opaque_have_term_bad", false);
measured_case!(have_exact_bad, "opaque_have_exact_bad", false);
measured_case!(let_term_ok, "opaque_let_term_ok", true);
measured_case!(let_exact_ok, "opaque_let_exact_ok", true);
measured_case!(have_nested_bad, "opaque_have_nested_bad", false);
measured_case!(let_nested_ok, "opaque_let_nested_ok", true);
measured_case!(have_rollback_ok, "opaque_have_rollback_ok", true);

// These original hypothesis names are retained byte-for-byte. All three are
// actual native positives; value-bearing induction targets are generalized.
measured_case!(
    nested_have_forbidden_bad,
    "opaque_nested_have_forbidden_bad",
    true
);
measured_case!(
    nested_have_induction_ok,
    "opaque_nested_have_induction_ok",
    true
);
measured_case!(
    nested_let_forbidden_bad,
    "opaque_nested_let_forbidden_bad",
    true
);

#[test]
fn nested_have_keeps_checked_raw_proof_with_capture_off_and_on() {
    let source = "def opaque_nested_identity (b : Bool) : Bool := by\n  have h : Bool := b\n  exact (by\n    exact h)\n";
    let name = Name::from_string("opaque_nested_identity");
    let mut bodies = Vec::new();
    for observe in [false, true] {
        let mut env = Environment::with_prelude();
        let mut file = FileContext::new();
        let capture = TacticGoalCapture::default();
        if observe {
            file.set_tactic_goal_capture(Some(capture.clone()));
        }
        let declarations = parse_file_with_tactics(source, &builtin_tactic_patterns())
            .expect("actual nested source parses");
        for declaration in declarations {
            let declaration = preprocess_decl_with_context(&declaration, &mut file);
            elaborate_decl_and_register_with_context(&mut env, &declaration, &mut file)
                .expect("capture cannot change the normal declaration verdict");
        }
        let info = env.get_const(&name).expect("registered definition");
        let body = info.value.as_ref().expect("stored body");
        assert!(!body.has_fvar_quick() && !body.has_loose_bvars_quick());
        let tc = TypeChecker::new(&env);
        let ty = tc.infer_type_full(body).expect("full body inference");
        assert!(tc.is_def_eq(&ty, &info.type_));
        for constructor in ["Bool.false", "Bool.true"] {
            let input = Expr::const_(Name::from_string(constructor), vec![]);
            let application = Expr::app(Expr::const_(name.clone(), vec![]), input.clone());
            assert!(
                tc.is_def_eq(&application, &input),
                "actual Boolean identity"
            );
        }
        assert!(env.axiom_deps(&name).expect("stored closure").is_empty());
        bodies.push((info.type_.clone(), body.clone()));
        let views = capture.take().expect("actual passive collector");
        if !observe {
            assert!(views.is_empty());
            continue;
        }
        let nested: Vec<_> = views
            .iter()
            .filter(|view| view.kind == TacticGoalObservationKind::ByPrefix)
            .filter_map(|view| view.before.as_ref().ok())
            .flat_map(|view| &view.goals)
            .filter(|goal| {
                goal.local_ctx
                    .iter()
                    .any(|local| local.name.to_string() == "h")
            })
            .collect();
        assert_eq!(
            nested.len(),
            1,
            "the real nested by prefix, not a fabricated scope"
        );
        let locals = &nested[0].local_ctx;
        let b = locals
            .iter()
            .find(|local| local.name.to_string() == "b")
            .expect("same scoped b");
        let h = locals
            .iter()
            .find(|local| local.name.to_string() == "h")
            .expect("same scoped h");
        let proof = h
            .value
            .as_ref()
            .expect("a nested have retains its actual proof");
        let ExprKind::MData(data, proof) = proof.kind() else {
            panic!("missing have marker")
        };
        assert!(data
            .iter()
            .any(|(key, value)| key == &Name::from_string("_clean_have")
                && matches!(value, MDataValue::Bool(true))));
        assert_eq!(
            proof.as_ref(),
            &Expr::fvar(b.fvar),
            "raw proof keeps the original binder identity"
        );
    }
    assert_eq!(
        bodies[0], bodies[1],
        "observation cannot change stored public declarations"
    );
}
