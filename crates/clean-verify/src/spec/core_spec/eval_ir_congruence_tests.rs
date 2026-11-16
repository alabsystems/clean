// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::{eval_ir_state::IR_EQ_CONG_SOURCE, Specification};
use crate::test_utils::run_with_stack;
use clean_kernel::{Environment, Name};

fn check_congruence(mut spec: Specification) {
    spec.add_recursive_def(IR_EQ_CONG_SOURCE, "actual shared EvalIR congruence")
        .expect("explicit telescope must elaborate");
    spec.verify_definition("ir_eq_cong")
        .expect("independent kernel replay of shared congruence");
    let name = Name::from_string("ir_eq_cong");
    assert!(spec.env().axiom_deps(&name).unwrap().is_empty());
    assert!(spec.env().trust_marker_deps(&name).unwrap().is_empty());
    let invalid = IR_EQ_CONG_SOURCE
        .replace("def ir_eq_cong ", "def invalid_congruence ")
        .replace(
            "@Eq.subst A (fun (z : A) => @Eq B (f x) (f z)) x y h (@Eq.refl B (f x))",
            "@Eq.refl B (f y)",
        );
    assert_ne!(invalid, IR_EQ_CONG_SOURCE);
    spec.add_recursive_def(&invalid, "missing equality transport must refuse")
        .expect_err("reflexivity alone cannot identify distinct generic results");
    assert!(spec
        .env()
        .get_const(&Name::from_string("invalid_congruence"))
        .is_none());
}

#[test]
fn shared_congruence_explicit_telescope_checks_in_foundation() {
    run_with_stack(|| {
        let mut spec = Specification::new_empty();
        spec.add_foundation_types()
            .expect("foundation equality owner");
        check_congruence(spec);
    });
}

#[test]
fn shared_congruence_explicit_telescope_checks_in_production_prelude() {
    run_with_stack(|| {
        let mut spec = Specification::new_empty();
        spec.env = Environment::try_with_prelude().expect("ordinary production prelude");
        check_congruence(spec);
    });
}
