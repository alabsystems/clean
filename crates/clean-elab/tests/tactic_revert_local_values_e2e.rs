// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Exact sources measured on genuine Lean 4.30, 4.35 and 4.36-rc2.
//! Reverting a local definition keeps its value and forward let dependencies.

use clean_elab::tactic::builtins::builtin_tactic_patterns;
use clean_elab::{elaborate_decl_and_register, preprocess_decl_with_context, FileContext};
use clean_kernel::env::Environment;
use clean_kernel::{Name, TypeChecker};
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
                    "fixtures/revert_local_values/",
                    stringify!($case),
                    ".lean"
                )),
                $name,
                $accepts,
            );
        }
    };
}

measured_case!(selected_ok, "revert_let_selected_ok", true);
measured_case!(selected_bad, "revert_let_selected_bad", false);
measured_case!(chain_ok, "revert_let_chain_ok", true);
measured_case!(chain_bad, "revert_let_chain_bad", false);
measured_case!(outer_ok, "revert_let_outer_ok", true);
measured_case!(outer_bad, "revert_let_outer_bad", false);
measured_case!(ordinary_ok, "revert_let_ordinary_ok", true);
measured_case!(ordinary_bad, "revert_let_ordinary_bad", false);

measured_case!(intro_ok, "revert_let_intro_ok", true);
measured_case!(intro_bad, "revert_let_intro_bad", false);
measured_case!(intro_chain_ok, "revert_let_intro_chain_ok", true);
measured_case!(intro_chain_bad, "revert_let_intro_chain_bad", false);
measured_case!(cases_ok, "revert_let_cases_ok", true);
measured_case!(cases_bad, "revert_let_cases_bad", false);
measured_case!(induction_ok, "revert_let_induction_ok", true);
measured_case!(induction_bad, "revert_let_induction_bad", false);

measured_case!(dependent_ok, "revert_let_dependent_ok", true);
measured_case!(dependent_bad, "revert_let_dependent_bad", false);

measured_case!(type_value_bad, "revert_let_type_value_dependent_bad", false);
measured_case!(
    type_value_chain_bad,
    "revert_let_type_value_chain_dependent_bad",
    false
);
measured_case!(
    type_value_chain_ok,
    "revert_let_type_value_chain_dependent_ok",
    true
);
measured_case!(type_value_ok, "revert_let_type_value_dependent_ok", true);
measured_case!(
    value_chain_bad,
    "revert_let_value_chain_dependent_bad",
    false
);
measured_case!(value_chain_ok, "revert_let_value_chain_dependent_ok", true);
measured_case!(have_parameter_ok, "revert_have_parameter_ok", true);
measured_case!(have_retained_bad, "revert_have_retained_bad", false);
measured_case!(let_parameter_bad, "revert_let_parameter_bad", false);
measured_case!(let_retained_ok, "revert_let_retained_ok", true);

// Opaque have values do not create forward dependencies; genuine lets do.
measured_case!(
    opaque_have_retained_ok,
    "opaque_dependency_have_retained_ok",
    true
);
measured_case!(
    opaque_have_parameter_bad,
    "opaque_dependency_have_parameter_bad",
    false
);
measured_case!(
    opaque_let_retained_bad,
    "opaque_dependency_let_retained_bad",
    false
);
measured_case!(
    opaque_let_reintroduced_ok,
    "opaque_dependency_let_reintroduced_ok",
    true
);

measured_case!(
    opaque_have_induction_ok,
    "opaque_dependency_have_induction_ok",
    true
);
measured_case!(
    opaque_let_induction_bad,
    "opaque_dependency_let_induction_bad",
    false
);
