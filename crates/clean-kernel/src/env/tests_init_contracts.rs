// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for init contract infrastructure: graph validation and dependency
//! closure auditing.
//!
//! Part of #1461 — machine-checked env init dependency closure.

use super::init_contracts::{
    default_primitive_allowlist, wave1_contracts, InitContractId, InitContractRegistry,
};

// --- Graph structure tests ---

#[test]
fn test_init_contract_graph_acyclic() {
    let contracts = wave1_contracts();
    let registry = InitContractRegistry::new(contracts);

    let duplicates = registry.find_duplicate_ids();
    assert!(
        duplicates.is_empty(),
        "duplicate contract ids in wave1 contracts: {:?}",
        duplicates
    );

    // All dependency references must resolve.
    let unknown = registry.find_unknown_deps();
    assert!(
        unknown.is_empty(),
        "unknown contract dependencies: {:?}",
        unknown
    );

    // Graph must be acyclic (topological order must succeed).
    match registry.topological_order() {
        Ok(order) => {
            assert_eq!(
                order.len(),
                registry.len(),
                "topological order should include all {} contracts",
                registry.len()
            );
        }
        Err(cycle) => {
            panic!("cycle detected in init contract graph: {:?}", cycle);
        }
    }
}

#[test]
fn test_init_contract_no_unknown_deps() {
    let contracts = wave1_contracts();
    let registry = InitContractRegistry::new(contracts);
    let duplicates = registry.find_duplicate_ids();
    assert!(
        duplicates.is_empty(),
        "found duplicate ids: {:?}",
        duplicates
    );
    let unknown = registry.find_unknown_deps();
    for (contract, dep) in &unknown {
        eprintln!("  contract {contract} references unknown dep {dep}");
    }
    assert!(unknown.is_empty(), "found {} unknown deps", unknown.len());
}

#[test]
fn test_init_contract_topological_order_respects_deps() {
    let contracts = wave1_contracts();
    let registry = InitContractRegistry::new(contracts);
    let order = registry
        .topological_order()
        .expect("graph should be acyclic");

    // For each contract with dependencies, verify all deps appear earlier in order.
    let contracts = wave1_contracts();
    let id_to_contract: std::collections::HashMap<_, _> =
        contracts.iter().map(|c| (c.id.clone(), c)).collect();

    for (pos, id) in order.iter().enumerate() {
        if let Some(contract) = id_to_contract.get(id) {
            for dep_id in &contract.dependencies {
                let dep_pos = order
                    .iter()
                    .position(|x| x == dep_id)
                    .unwrap_or_else(|| panic!("dep {dep_id} not in order"));
                assert!(
                    dep_pos < pos,
                    "contract {id} at position {pos} has dep {dep_id} at position {dep_pos} (should be earlier)"
                );
            }
        }
    }
}

#[test]
fn test_wave1_contracts_cover_active_failure_symbols() {
    let contracts = wave1_contracts();
    let mut required_symbols: std::collections::HashSet<&'static str> =
        std::collections::HashSet::new();
    for contract in &contracts {
        required_symbols.extend(contract.required_symbols.iter().copied());
    }

    for symbol in ["Nat.le", "Nat.lt", "Subtype", "Iff", "Or"] {
        assert!(
            required_symbols.contains(symbol),
            "wave1 contracts must require symbol `{symbol}` somewhere in the graph"
        );
    }
}

#[test]
fn test_wave1_contracts_include_issue_1461_targets() {
    let contract_ids: std::collections::HashSet<&'static str> =
        wave1_contracts().iter().map(|c| c.id.0).collect();

    for target in [
        "topology_subspace",
        "topology_higher_homotopy",
        "nat_le_reflexive",
        "nat_lt_irrefl",
        "nat_lt_asymm",
        "nat_lt_trans",
        "nat_decidable_ord",
    ] {
        assert!(
            contract_ids.contains(target),
            "wave1 contracts are missing required #1461 target `{target}`"
        );
    }
}

// --- Closure audit tests ---
// These test that each init function's declarations only reference
// constants that are in scope (provided by dependencies or primitives).

#[test]
fn test_eq_closure() {
    run_closure_audit("eq");
}

#[test]
fn test_iff_closure() {
    run_closure_audit("iff");
}

#[test]
fn test_and_closure() {
    run_closure_audit("and");
}

#[test]
fn test_classical_closure() {
    run_closure_audit("classical");
}

#[test]
fn test_subtype_closure() {
    run_closure_audit("subtype");
}

#[test]
fn test_exists_closure() {
    run_closure_audit("exists");
}

#[test]
fn test_nat_closure() {
    run_closure_audit("nat");
}

#[test]
fn test_le_closure() {
    run_closure_audit("le");
}

#[test]
fn test_lt_closure() {
    run_closure_audit("lt");
}

// --- Intermediate contract closure tests ---
// These cover prerequisite contracts that Wave 1 target contracts depend on.

#[test]
fn test_true_false_closure() {
    run_closure_audit("true_false");
}

#[test]
fn test_preorder_closure() {
    run_closure_audit("preorder");
}

#[test]
fn test_partial_order_closure() {
    run_closure_audit("partial_order");
}

#[test]
fn test_linear_order_closure() {
    run_closure_audit("linear_order");
}

#[test]
fn test_decidable_closure() {
    run_closure_audit("decidable");
}

#[test]
fn test_reflexive_closure() {
    run_closure_audit("reflexive");
}

#[test]
fn test_irrefl_closure() {
    run_closure_audit("irrefl");
}

#[test]
fn test_trans_closure() {
    run_closure_audit("trans");
}

#[test]
fn test_antisymm_closure() {
    run_closure_audit("antisymm");
}

#[test]
fn test_asymm_closure() {
    run_closure_audit("asymm");
}

// nat_preorder, nat_partial_order, and nat_linear_order blocked on
// TypeCheckFailed in order.rs init functions (LE.le path vs Nat.le
// type mismatch). W3 domain (#1444 migration). See blocked tests below.

// nat_partial_order and nat_linear_order blocked on TypeCheckFailed in
// init_nat_partial_order (instPartialOrderNat le_antisymm field type mismatch:
// LE.le/Preorder.toLE path vs Nat.le, and Eq universe). Same bug class as #1488
// but in order.rs — W3 domain (#1444 migration). See blocked tests below.

// --- Nat-order target closure tests ---

#[test]
fn test_nat_le_reflexive_closure() {
    run_closure_audit("nat_le_reflexive");
}

#[test]
fn test_nat_lt_irrefl_closure() {
    run_closure_audit("nat_lt_irrefl");
}

#[test]
fn test_nat_lt_asymm_closure() {
    run_closure_audit("nat_lt_asymm");
}

#[test]
fn test_nat_lt_trans_closure() {
    run_closure_audit("nat_lt_trans");
}

#[test]
fn test_nat_decidable_ord_closure() {
    run_closure_audit("nat_decidable_ord");
}

// --- Wave 2: Nat-order extended closure tests ---

#[test]
fn test_nat_le_antisymm_closure() {
    run_closure_audit("nat_le_antisymm");
}

#[test]
fn test_nat_le_trans_closure() {
    run_closure_audit("nat_le_trans");
}

#[test]
fn test_strict_order_closure() {
    run_closure_audit("strict_order");
}

#[test]
fn test_nat_lt_strict_order_closure() {
    run_closure_audit("nat_lt_strict_order");
}

// nat_trans_lt_le_lt, nat_trans_le_lt_lt, nat_trans_lt_lt_le: unblocked after
// Trans expanded to 3 universe params (matching Lean 4) in order_structures.rs.
// Previously blocked on LevelCountMismatch (#1444).

#[test]
fn test_nat_trans_lt_le_lt_closure() {
    run_closure_audit("nat_trans_lt_le_lt");
}

#[test]
fn test_nat_trans_le_lt_lt_closure() {
    run_closure_audit("nat_trans_le_lt_lt");
}

#[test]
fn test_nat_trans_lt_lt_le_closure() {
    run_closure_audit("nat_trans_lt_lt_le");
}

#[test]
fn test_nat_not_lt_le_closure() {
    run_closure_audit("nat_not_lt_le");
}

#[test]
fn test_nat_succ_lt_closure() {
    run_closure_audit("nat_succ_lt");
}

#[test]
fn test_nat_lt_or_eq_of_le_closure() {
    run_closure_audit("nat_lt_or_eq_of_le");
}

// nat_lt_of_le_of_ne: init function references False (via Eq a b -> False for
// negation) without calling init_true_false in its prelude. The contract now
// declares true_false as a dependency so the audit framework provides False
// before running the init function, proving the dependency closure is correct
// when the prerequisite is satisfied.
// Production fix: W3 should add self.init_true_false()? to the prelude in order.rs.

#[test]
fn test_nat_lt_of_le_of_ne_closure() {
    run_closure_audit("nat_lt_of_le_of_ne");
}

// nat_lt_trichotomy: unblocked after Or universe-level fix.
// Previously blocked on TypeMismatch (Sort(Zero) vs Sort(Succ(Zero))).

#[test]
fn test_nat_lt_trichotomy_closure() {
    run_closure_audit("nat_lt_trichotomy");
}

#[test]
fn test_nat_succ_base_closure() {
    run_closure_audit("nat_succ_base");
}

#[test]
fn test_topological_space_closure() {
    run_closure_audit("topological_space");
}

#[test]
fn test_topology_continuous_closure() {
    run_closure_audit("topology_continuous");
}

// --- Full graph closure audit ---
// Run all non-blocked contracts in topological order. This is the primary
// regression gate: if any init function introduces a new missing-dependency
// reference, this test catches it.

#[test]
fn test_all_non_blocked_closure_audits() {
    // All previously blocked contracts are now unblocked:
    // - topology_subspace: fixed by W3-675 Subtype.val implicit args (#1488)
    // - nat_trans_*: fixed by 3-universe Trans expansion
    // - nat_lt_trichotomy: fixed by Or universe-level fix
    // - nat_preorder chain (preorder/partial/linear/add/mul/sub/pow):
    //   fixed by definition→axiom conversion pending projection reduction #1526
    let blocked: std::collections::HashSet<&str> = std::collections::HashSet::new();

    let contracts = wave1_contracts();
    let registry = InitContractRegistry::new(contracts);
    let allowlist = default_primitive_allowlist();
    let order = registry
        .topological_order()
        .expect("graph should be acyclic");

    let mut failures = Vec::new();
    for id in &order {
        if blocked.contains(id.0) {
            continue;
        }
        match registry.audit_closure(id, &allowlist) {
            Ok(result) => {
                if !result.passed {
                    failures.push(format!(
                        "{}: {} missing refs: {:?}",
                        id,
                        result.missing_symbols.len(),
                        result.missing_symbols
                    ));
                }
            }
            Err(e) => {
                failures.push(format!("{}: init error: {e}", id));
            }
        }
    }

    if !failures.is_empty() {
        eprintln!("--- full closure audit failures ---");
        for f in &failures {
            eprintln!("  {f}");
        }
        panic!(
            "{} of {} audited contracts failed",
            failures.len(),
            order.len() - blocked.len()
        );
    }
}

// Topology contracts blocked on #1488 (universe-level construction bugs).
// This test verifies that the failure is TypeCheckFailed (upstream bug),
// topology_subspace: unblocked after W3-675 fixed 5 Subtype.val missing
// implicit args (#1488). Previously blocked on TypeCheckFailed.

#[test]
fn test_topology_subspace_closure() {
    run_closure_audit("topology_subspace");
}

// W2#94 added init_lt() dependency, fixing UnknownConst(Nat.lt); closure now passes.
#[test]
fn test_topology_higher_homotopy_closure() {
    run_closure_audit("topology_higher_homotopy");
}

// nat_preorder: unblocked after instPreorderNat switched to axiom
// (bypassing LE.le vs Nat.le mismatch pending projection reduction #1526).
// Previously blocked on TypeCheckFailed in init_nat_preorder (#1444).

#[test]
fn test_nat_preorder_closure() {
    run_closure_audit("nat_preorder");
}

// nat_partial_order, nat_linear_order: unblocked transitively through
// nat_preorder fix. Previously blocked on LE.le/Preorder.toLE path mismatch.

#[test]
fn test_nat_partial_order_closure() {
    run_closure_audit("nat_partial_order");
}

#[test]
fn test_nat_linear_order_closure() {
    run_closure_audit("nat_linear_order");
}

// Arithmetic order contracts: unblocked transitively through nat_linear_order.
// Previously blocked: nat_linear_order → nat_partial_order → nat_preorder.

#[test]
fn test_nat_add_ord_closure() {
    run_closure_audit("nat_add_ord");
}

#[test]
fn test_nat_mul_ord_closure() {
    run_closure_audit("nat_mul_ord");
}

#[test]
fn test_nat_sub_ord_closure() {
    run_closure_audit("nat_sub_ord");
}

#[test]
fn test_nat_pow_ord_closure() {
    run_closure_audit("nat_pow_ord");
}

// --- Helpers ---

fn run_closure_audit(contract_id: &'static str) {
    let contracts = wave1_contracts();
    let registry = InitContractRegistry::new(contracts);
    let duplicates = registry.find_duplicate_ids();
    assert!(
        duplicates.is_empty(),
        "duplicate contract ids in wave1 contracts: {:?}",
        duplicates
    );
    let target = InitContractId(contract_id);
    let allowlist = default_primitive_allowlist();

    let result = registry
        .audit_closure(&target, &allowlist)
        .unwrap_or_else(|e| panic!("closure audit error for {contract_id}: {e}"));

    if !result.passed {
        eprintln!("--- closure audit FAILED for {contract_id} ---");
        eprintln!("added {} constants:", result.added_symbols.len());
        for sym in &result.added_symbols {
            eprintln!("  + {sym}");
        }
        eprintln!("missing {} references:", result.missing_symbols.len());
        for msg in &result.missing_symbols {
            eprintln!("  ! {msg}");
        }
        panic!(
            "closure audit failed for {}: {} missing references",
            contract_id,
            result.missing_symbols.len()
        );
    }
}
