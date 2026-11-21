// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recheck the actual source declarations used by parity reconstruction.

use clean_kernel::{env::Environment, name::Name};

#[test]
fn actual_parity_ingredients_have_strict_production_closure() {
    let env = Environment::with_prelude();
    for name in ["Nat.div2_rejoin", "Nat.add_comm", "Nat.add_sub_cancel"] {
        let declaration = env
            .get_const(&Name::from_string(name))
            .expect("actual source declaration");
        let proof = declaration.value.as_ref().expect("actual proof body");
        let audit = env.audit_certification(&declaration.type_, proof);
        assert!(audit.is_certified(), "{name}: {:?}", audit.issues);
    }
}
