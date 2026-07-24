// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
//! Smoke test: Nat.eq_of_beq_eq_true is present in the default with_prelude env
//! (registered alongside the ble/le bridge in init_decidable_eq).
use clean_kernel::env::Environment;
use clean_kernel::name::Name;

#[test]
fn eq_of_beq_present_in_prelude() {
    let env = Environment::with_prelude();
    assert!(
        env.get_const(&Name::from_string("Nat.eq_of_beq_eq_true"))
            .is_some(),
        "Nat.eq_of_beq_eq_true must be in the default prelude"
    );
    // and the ble bridge (comparison monitors) as a control
    assert!(
        env.get_const(&Name::from_string("Nat.le_of_ble_eq_true"))
            .is_some(),
        "Nat.le_of_ble_eq_true (control) must be in the default prelude"
    );
    // AXIOM-FREEDOM (2026-07-13 true-state audit: this test previously asserted
    // only PRESENCE while the campaign record claimed axiom-freedom was
    // asserted here — close that gap): both monitor bridge lemmas must be
    // constructive, with an EMPTY transitive axiom closure.
    for name in ["Nat.eq_of_beq_eq_true", "Nat.le_of_ble_eq_true"] {
        let deps = env
            .axiom_deps(&Name::from_string(name))
            .expect("lemma registered");
        let names: Vec<String> = deps.iter().map(ToString::to_string).collect();
        assert!(names.is_empty(), "{name} must be axiom-free, got {names:?}");
    }
}
