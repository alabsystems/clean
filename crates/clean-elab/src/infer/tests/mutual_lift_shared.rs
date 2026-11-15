// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Gap G23 / ledger class (92), brick B2: SHARED recursor slots (several
//! members own one slot: a `PProd` tuple, or `And` for theorems) and
//! TRANSPARENT INTERMEDIATE slots (`Nat × C` / `String × C` under constant
//! motives), through the production entry `elaborate_decl_and_register`.
//!
//! Fixtures and their pinned verdicts are those of `mutual_lift.rs`
//! (`tests/fixtures/mutual_nested/`, `verdicts.json` re-derived by
//! `scripts/mutual_nested_verdicts.py`). Every accepted shape carries a
//! Lean-refused twin, and the shared slots carry a MIS-WIRING control: a
//! statement that would hold only if one owner were wired to another, which
//! the kernel alone cannot rule out when the owners share a type.

use super::mutual_lift_tests::{
    accepts_all, assert_lifted, assert_widening, fixture, fresh, lean_accepts, refused_by_lift,
    refuses_last, registered, run_file, value_constants,
};
use super::*;
use clean_kernel::env::Environment;

/// The registry entry of a lifted member.
fn entry(env: &mut Environment, member: &str) -> mutual_lift::MutualLiftEntry {
    env.get_ext_state_or_init::<crate::MutualLiftState>(crate::mutual_lift_idx())
        .and_then(|state| state.get(&Name::from_string(member)).cloned())
        .unwrap_or_else(|| panic!("`{member}` has a registry entry"))
}

/// `(owner index, owner count)` of each member, in order.
fn assert_owners(env: &mut Environment, expected: &[(&str, usize, usize)]) {
    for (member, index, count) in expected {
        let entry = entry(env, member);
        assert_eq!(
            (entry.owner_index, entry.owner_count),
            (*index, *count),
            "`{member}`'s place among its slot's owners"
        );
    }
}

/// Accepted with every declaration, and its twin refused at its last one.
fn accepted_with_twin(fixture: (&str, &str), twin: (&str, &str), last: &str) -> Environment {
    assert!(lean_accepts(fixture.0), "{}: Lean accepts it", fixture.0);
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert!(!lean_accepts(twin.0), "{}: Lean refuses it", twin.0);
    let err = refuses_last(&mut fresh(), twin, last);
    assert!(
        !err.contains("mutual structural recursion"),
        "{}: the block lifts and the false claim is what is refused: {err}",
        twin.0
    );
    env
}

#[test]
fn test_mutual_lift_shared_slot_pprod_decide() {
    let mut env = accepted_with_twin(
        fixture!("shared_slot_eval.lean"),
        fixture!("shared_slot_eval_twin.lean"),
        "e1_twin",
    );
    for name in ["e1", "e2"] {
        assert!(registered(&env, name), "`{name}` registered");
    }
    assert_lifted(&mut env, &["P.eval", "P.all", "P.any"], "P.rec");
    assert_owners(
        &mut env,
        &[("P.eval", 0, 1), ("P.all", 0, 2), ("P.any", 1, 2)],
    );
    assert!(
        value_constants(&env, "P.any").contains(&Name::from_string("PProd")),
        "the shared `List P` slot's motive is a `PProd` pair"
    );
}

/// Judge k3: `:= True.intro` / `:= id` through the shared slot with `v` open, and
/// the mis-wiring control `dn` (holds only if `denoteAny` were `denoteAll`).
#[test]
fn test_mutual_lift_shared_denote_open_value_and_miswire_control() {
    let fixture = fixture!("shared_denote.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    for name in ["dt", "db", "dc"] {
        assert!(registered(&env, name), "`{name}` registered");
    }
    assert_lifted(
        &mut env,
        &["Q.denote", "Q.denoteAll", "Q.denoteAny"],
        "Q.rec",
    );
    assert_owners(
        &mut env,
        &[
            ("Q.denote", 0, 1),
            ("Q.denoteAll", 0, 2),
            ("Q.denoteAny", 1, 2),
        ],
    );
    for member in ["Q.denote", "Q.denoteAll", "Q.denoteAny"] {
        let entry = entry(&mut env, member);
        assert_eq!(entry.fixed_arity, 1, "`{member}` keeps `k` fixed");
        assert_eq!(entry.major_param, 1);
        assert_eq!(
            entry.rest_params,
            vec![2],
            "`{member}` takes `v` after the major"
        );
    }
    let miswire = fixture!("shared_denote_miswire.lean");
    assert!(!lean_accepts(miswire.0));
    let err = refuses_last(&mut fresh(), miswire, "dn");
    assert!(!err.contains("mutual structural recursion"), "{err}");
}

/// Judge j2_denote: trust-ir's `Pred.denote` shape (fixed `U m`, an inner
/// `match U`, `List P` owned twice), `denote_Top := True.intro` at open `U m v`.
#[test]
fn test_mutual_lift_shared_denote_fixed_prefix_inner_match() {
    let mut env = accepted_with_twin(
        fixture!("shared_denote_fixed.lean"),
        fixture!("shared_denote_fixed_twin.lean"),
        "denote_Disj_nil",
    );
    assert!(registered(&env, "denote_Top"));
    assert_lifted(
        &mut env,
        &["P.denote", "P.denoteAll", "P.denoteAny"],
        "P.rec",
    );
    for member in ["P.denote", "P.denoteAll", "P.denoteAny"] {
        assert_eq!(
            entry(&mut env, member).fixed_arity,
            2,
            "`{member}` keeps `U m`"
        );
    }
}

/// Judge k2 g1/g2 and the B1 pin `open_pair_intermediate`: recursion through
/// the pair intermediate `Nat × C`; a grandchild is counted exactly once.
#[test]
fn test_mutual_lift_pair_intermediate_decide() {
    let mut env = accepted_with_twin(
        fixture!("pair_intermediate_size.lean"),
        fixture!("pair_intermediate_size_twin.lean"),
        "s1_twin",
    );
    assert_lifted(&mut env, &["C.size", "C.fieldsSmall"], "C.rec");
    let mut env = accepted_with_twin(
        fixture!("pair_decide.lean"),
        fixture!("pair_decide_twin.lean"),
        "g1f",
    );
    assert_lifted(&mut env, &["C.sz", "C.fsz"], "C.rec");
    let grandchild = fixture!("pair_wrong_grandchild.lean");
    assert!(!lean_accepts(grandchild.0));
    let err = refuses_last(&mut fresh(), grandchild, "bad");
    assert!(
        err.contains("decide"),
        "refused by `decide` evaluating false: {err}"
    );
}

/// Widening (docs/DECISIONS.md R45, judge k2 g3r): the defining equation
/// through the pair holds by `rfl` on open terms.
#[test]
fn test_mutual_lift_pair_rfl_widening_with_false_twin() {
    let fixture = fixture!("pair_rfl_widening.lean");
    assert_widening(fixture.0);
    accepts_all(&mut fresh(), fixture);
    let twin = fixture!("pair_rfl_widening_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "g3r_twin");
}

/// Block 1 (trust-ir Constant.lean:146): out-of-order arms over `List C`
/// and `List (String × C)`. The large-constant `decide` is a widening: Lean
/// 4.8 stops it at maxRecDepth (judge j1_constant).
#[test]
fn test_mutual_lift_symbol_addr_block() {
    let mut env = accepted_with_twin(
        fixture!("symbol_addr.lean"),
        fixture!("symbol_addr_twin.lean"),
        "h3_twin",
    );
    assert_lifted(&mut env, &["C.has", "C.lhas", "C.fhas"], "C.rec");
    let wide = fixture!("symbol_addr_widening.lean");
    assert_widening(wide.0);
    accepts_all(&mut fresh(), wide);
    let twin = fixture!("symbol_addr_widening_twin.lean");
    assert!(!lean_accepts(twin.0));
    refuses_last(&mut fresh(), twin, "t1_twin");
}

/// Block 8 (trust-ir Semantics/Step.lean:75): `List C` owned by two members
/// whose leading parameters differ; the major is the second parameter.
#[test]
fn test_mutual_lift_const_value_at_block() {
    let mut env = accepted_with_twin(
        fixture!("const_value_at.lean"),
        fixture!("const_value_at_twin.lean"),
        "v2_twin",
    );
    let block = ["constValueAt", "constFieldsAt", "constLanesAt"];
    assert_lifted(&mut env, &block, "C.rec");
    assert_owners(
        &mut env,
        &[
            ("constValueAt", 0, 1),
            ("constFieldsAt", 0, 2),
            ("constLanesAt", 1, 2),
        ],
    );
    for member in block {
        let entry = entry(&mut env, member);
        assert_eq!(entry.fixed_arity, 0, "`{member}`: no fixed prefix");
        assert_eq!(
            entry.major_param, 1,
            "`{member}` recurses on its second parameter"
        );
        assert_eq!(entry.rest_params, vec![0]);
    }
}

/// Block 7 (trust-ir Semantics/Aggregate.lean:594): the pair intermediate
/// whose first component the result keeps.
#[test]
fn test_mutual_lift_of_constant_block() {
    let mut env = accepted_with_twin(
        fixture!("of_constant.lean"),
        fixture!("of_constant_twin.lean"),
        "o1_twin",
    );
    assert_lifted(
        &mut env,
        &["V.ofConstant", "V.ofConstantList", "V.ofConstantFieldList"],
        "C.rec",
    );
}

/// Block 9 (trust-ir Semantics/Step.lean:121): or-patterns and the pair.
#[test]
fn test_mutual_lift_inexact_float_or_patterns_block() {
    let mut env = accepted_with_twin(
        fixture!("inexact_float.lean"),
        fixture!("inexact_float_twin.lean"),
        "i1_twin",
    );
    assert_lifted(
        &mut env,
        &[
            "constHasInexactFloat",
            "constListHasInexactFloat",
            "constFieldListHasInexactFloat",
        ],
        "C.rec",
    );
}

/// A theorem block sharing `List Q`: its `Prop` slot is an `And` pair; the
/// non-structural twin is refused by the lift.
#[test]
fn test_mutual_lift_shared_theorem_slot_and_chain() {
    let fixture = fixture!("shared_theorems.lean");
    assert!(lean_accepts(fixture.0));
    let mut env = fresh();
    accepts_all(&mut env, fixture);
    assert_lifted(&mut env, &["Q.r", "Q.ra", "Q.rb"], "Q.rec");
    assert_owners(&mut env, &[("Q.r", 0, 1), ("Q.ra", 0, 2), ("Q.rb", 1, 2)]);
    let consts = value_constants(&env, "Q.rb");
    assert!(
        consts.contains(&Name::from_string("And")) && !consts.contains(&Name::from_string("PProd")),
        "a theorem block pairs with `And`: {consts:?}"
    );
    refused_by_lift(
        &mut fresh(),
        fixture!("shared_theorems_nonstruct.lean"),
        &["Q.r", "Q.ra", "Q.rb"],
        "Q.rb",
    );
}

/// OPEN, pinned as a refusal Lean does not share (design §9): fails the day
/// it closes — then re-file ledger class (92) and turn the pin into a PASS
/// test with its negative control.
fn open_shape(fixture: (&str, &str), block: &[&str], reason: &str) {
    assert!(lean_accepts(fixture.0), "{}: Lean accepts it", fixture.0);
    let mut env = fresh();
    let outcomes = run_file(&mut env, fixture.1);
    let err = match outcomes.iter().find_map(|o| o.as_ref().err()) {
        Some(err) => err.clone(),
        None => panic!(
            "OPEN gap closed: {} now elaborates. Re-file ledger class (92) and turn \
             this pin into a PASS test with a negative control.",
            fixture.0
        ),
    };
    assert!(
        err.contains("mutual structural recursion") && err.contains(reason),
        "{}: refused by the lift for `{reason}`: {err}",
        fixture.0
    );
    assert!(!err.contains("Unknown constant"), "{err}");
    for member in block {
        assert!(
            !registered(&env, member),
            "`{member}` must not be registered"
        );
    }
}

/// Judge k7: `P.f p` on the head of the owned `List P` field.
#[test]
fn test_mutual_lift_course_of_values_through_owned_slot_is_open() {
    open_shape(
        fixture!("open_cov_through_owned.lean"),
        &["P.f", "P.g"],
        "a variable bound inside the body",
    );
}

/// A dependent motive cannot pass through the pair intermediate.
#[test]
fn test_mutual_lift_dependent_theorem_through_pair_is_open() {
    let fixture = fixture!("open_pair_dependent_theorem.lean");
    open_shape(
        fixture,
        &["C.sz_self", "C.fsz_self"],
        "dependent motive through an intermediate",
    );
    let mut env = fresh();
    let _ = run_file(&mut env, fixture.1);
    assert!(
        registered(&env, "C.sz") && registered(&env, "C.fsz"),
        "the data block before the theorem block lifts"
    );
}

/// `Option O` is a multi-constructor intermediate.
#[test]
fn test_mutual_lift_option_intermediate_is_open() {
    open_shape(
        fixture!("open_option_intermediate.lean"),
        &["O.f", "O.fl"],
        "a variable bound inside the body",
    );
}
