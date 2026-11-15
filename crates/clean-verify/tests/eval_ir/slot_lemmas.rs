// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! **Phase-B's return-slot stage** — the acceptance gate for
//! `add_eval_ir_slot_lemmas`.
//!
//! The probe that established these terms ran in `evalir_scratchpad`, which is
//! a development tool and explicitly not a gate (an absent or empty scratch
//! file passes trivially). This file is where the same terms become a standing
//! claim: registered by a bundle, resting on nothing, and pinned by name.

use std::collections::BTreeSet;

use clean_kernel::Name;
use clean_verify::spec::SLOT_LEMMA_NAMES;
use clean_verify::test_utils::build_eval_ir_spec_with_stack;
use clean_verify::vacuity_firewall::env_knows;

use super::census::{SLOT_LEMMAS, SLOT_PREFIX_NOT_FROM_THE_STAGE};

/// **Phase-B's return-slot stage, registered and resting on nothing.**
///
/// `add_eval_ir_slot_lemmas` closes the `alloca` / `store` / `load` / `ret`
/// pattern at an ABSTRACT heap and an ABSTRACT allocation counter — the shape
/// every callee body in the derived bundle (`Option::as_deref`,
/// `Option::expect`, `<Arc<T>>::deref`) opens with. The probe that established
/// it ran in the scratchpad, which is a development tool and not a gate; this
/// is where the same terms become a standing claim.
///
/// Three clauses:
///
/// 1. Every listed declaration is in the EvalIr bundle, and its transitive
///    axiom closure is empty in BOTH halves. `Environment::axiom_deps` does not
///    on its own establish that: it returns the closure MINUS the foundational
///    axioms, so an empty result means "no domain axiom and no trust marker",
///    and a proof resting on `Classical.choice` passes it. The complement is
///    `foundational_axiom_deps`, and the kernel documents the two as
///    partitioning the full closure
///    (`clean-kernel/src/env/axiom_audit.rs`, `axiom_closure_all`); asserting
///    both empty is what makes the closure empty. These are inductions and
///    transports over reducible definitions, so anything in either half would
///    mean a fact the semantics assumes rather than computes.
/// 2. The census copy of the list IS the stage's own registration list. The
///    stage publishes `SLOT_LEMMA_NAMES` and registers that table and nothing
///    else, so this clause covers EVERY declaration it adds — the five
///    substrate lemmas (`ir_nat_sub_self`, `ir_nat_eqb_refl`,
///    `ir_mem_lookup_head`, `ir_mem_update_head`, `ir_mem_lookup_skip`)
///    included. It used to be scoped to the `ir_slot_` prefix on both sides,
///    which pinned 21 of the 26 and said nothing about those five.
/// 3. The `ir_slot_` prefix is additionally pinned EXACTLY, not inclusively,
///    against the built environment: the registered set is the stage's list
///    plus `ir_slot_live` (`add_eval_ir`'s liveness projection, which predates
///    the stage) and nothing else. That is the clause that catches a lemma
///    registered under the family's prefix by some OTHER stage.
#[test]
fn eval_ir_slot_lemmas_are_registered() {
    let spec = build_eval_ir_spec_with_stack();

    for name in SLOT_LEMMAS {
        assert!(
            env_knows(spec.env(), name),
            "{name} must be registered by the EvalIr bundle's slot-lemma stage"
        );
        // Both halves resolve or the clause is VACUOUS: `axiom_deps` keys on
        // `get_const` while `env_knows` above also accepts an inductive, so an
        // `unwrap_or_default()` here would read "not a constant" as "empty
        // closure" and pass. Refuse instead of defaulting.
        let key = Name::from_string(name);
        let mut domain: Vec<String> = spec
            .env()
            .axiom_deps(&key)
            .unwrap_or_else(|| panic!("{name} has no constant entry, so its axiom closure is not computable — an empty answer here would be vacuous"))
            .into_iter()
            .map(|n| n.to_string())
            .collect();
        domain.sort();
        let mut foundational: Vec<String> = spec
            .env()
            .foundational_axiom_deps(&key)
            .unwrap_or_else(|| {
                panic!(
                    "{name} has no constant entry, so its foundational closure is not computable"
                )
            })
            .into_iter()
            .map(|n| n.to_string())
            .collect();
        foundational.sort();
        assert!(
            domain.is_empty(),
            "{name} must reach no domain-specific axiom and no trust marker — it is a \
             computation and two inductions, not an assumption. Found: {domain:?}"
        );
        assert!(
            foundational.is_empty(),
            "{name} must reach no FOUNDATIONAL axiom either; together with the clause above \
             that is what makes its transitive axiom closure empty. Found: {foundational:?}"
        );
    }

    // Clause 2: the census copy is the stage's own registration list, in order.
    // Not a prefix filter — this is what covers the five substrate lemmas.
    assert_eq!(
        SLOT_LEMMAS, SLOT_LEMMA_NAMES,
        "census.rs's SLOT_LEMMAS is no longer the list `add_eval_ir_slot_lemmas` registers. \
         The stage's DECLS table is the authority; update the census copy to match it (and \
         re-run `python3 scripts/gen_slot_lemmas.py --check`) rather than relaxing this."
    );

    // Clause 3: nothing else in the bundle claims the family's prefix.
    let registered: BTreeSet<&str> = spec
        .definitions()
        .keys()
        .map(String::as_str)
        .filter(|n| n.starts_with("ir_slot_"))
        .collect();
    let expected: BTreeSet<&str> = SLOT_LEMMAS
        .iter()
        .chain(SLOT_PREFIX_NOT_FROM_THE_STAGE)
        .copied()
        .filter(|n| n.starts_with("ir_slot_"))
        .collect();
    assert_eq!(
        registered, expected,
        "the `ir_slot_` declarations moved. Add the new lemma to the stage's DECLS table and \
         to census.rs's SLOT_LEMMAS rather than relaxing this assertion."
    );
}
