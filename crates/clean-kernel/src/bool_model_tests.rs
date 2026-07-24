// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for the generic Boolean-model layer: the model definitions reduce as
//! specified and the consistency/exclusivity theorems are PROVED (axiom closure
//! ⊆ FOUNDATIONAL_AXIOMS).

use super::names;
use crate::name::Name;
use crate::{ConstantKind, Environment};

fn model_env() -> Environment {
    let mut env = Environment::with_prelude();
    env.init_bool_model().expect("init_bool_model");
    env
}

#[test]
fn bool_model_layer_initializes() {
    let env = model_env();
    for n in [
        names::ODDP,
        names::HALF,
        names::BOOL_MODEL_LIT,
        names::BOOL_MODEL,
        names::HALF_ODD_LIT_NEG,
        names::BOOL_MODEL_LIT_NEG,
        names::BOOL_MODEL_CONSISTENT,
        names::BOOL_MODEL_EXCLUSIVE,
    ] {
        assert!(
            env.get_const(&Name::from_string(n)).is_some(),
            "{n} must be registered"
        );
    }
}

#[test]
fn model_theorems_are_proved_zero_domain_axioms() {
    let env = model_env();
    for n in [
        names::HALF_ODD_LIT_NEG,
        names::BOOL_MODEL_LIT_NEG,
        names::BOOL_MODEL_CONSISTENT,
        names::BOOL_MODEL_EXCLUSIVE,
    ] {
        let nm = Name::from_string(n);
        let info = env.get_const(&nm).expect("registered");
        assert!(
            matches!(info.kind, ConstantKind::Theorem),
            "{n} must be a Theorem"
        );
        let domain = env.axiom_deps(&nm).expect("axiom_deps");
        assert!(
            domain.is_empty(),
            "{n} must have ZERO domain axioms; got {domain:?}"
        );
    }
}
