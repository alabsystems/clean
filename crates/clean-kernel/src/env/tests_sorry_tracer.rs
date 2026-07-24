// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for sorry dependency tracer.
//!
//! Extracted from `sorry_tracer.rs` to keep that file under the 500-line
//! project limit after the drift regression tests added for #3560.

use super::axiom_audit::{is_foundational_axiom, ADMITTED_DOMAIN_AXIOMS, FOUNDATIONAL_AXIOMS};
use super::sorry_tracer::{is_sorry_axiom, SorryTracer};
use super::types::{ConstantInfo, ConstantKind, Reducibility};
use super::Environment;
use crate::expr::Expr;
use crate::name::Name;
use crate::Declaration;

/// Helper: create a fresh environment.
fn fresh_env() -> Environment {
    Environment::new()
}

/// Helper: add a domain-specific axiom (sorry obligation).
fn add_sorry_axiom(env: &mut Environment, name: &str, type_: Expr) {
    let decl = Declaration::Axiom {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
    };
    env.add_decl(decl).expect("axiom should be added");
}

/// Helper: add a definition that references other constants.
fn add_definition(env: &mut Environment, name: &str, type_: Expr, value: Expr) {
    let decl = Declaration::Definition {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value,
        is_reducible: true,
    };
    // Use add_decl_structural since type checking may fail for synthetic exprs
    env.add_decl_structural(decl)
        .expect("definition should be added");
}

/// Helper: add a theorem that references other constants.
fn add_theorem(env: &mut Environment, name: &str, type_: Expr, proof: Expr) {
    let decl = Declaration::Theorem {
        name: Name::from_string(name),
        level_params: vec![],
        type_,
        value: proof,
    };
    env.add_decl_structural(decl)
        .expect("theorem should be added");
}

/// Helper: build a synthetic axiom `ConstantInfo` for classifier-driver tests.
fn synth_axiom_info(name: &str) -> ConstantInfo {
    ConstantInfo::new_with_reducibility(
        Name::from_string(name),
        vec![],
        Expr::prop(),
        None,
        Reducibility::Regular(0),
        ConstantKind::Axiom,
    )
}

// ---- Test: empty environment ----

#[test]
fn test_sorry_tracer_empty_env() {
    let env = fresh_env();
    let tracer = SorryTracer::build(&env);
    // Even an empty env might have built-in axioms, but no domain-specific sorry
    // The priority list should only contain sorry axioms (non-foundational)
    for (name, _) in tracer.priority() {
        assert!(
            !is_foundational_axiom(name),
            "foundational axiom {} should not appear in sorry priority",
            name
        );
    }
}

// ---- Test: single sorry axiom with no dependents ----

#[test]
fn test_sorry_tracer_single_sorry_no_dependents() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "my_sorry", Expr::prop());
    let tracer = SorryTracer::build(&env);

    let impact = tracer.impact(&Name::from_string("my_sorry"));
    // No other declarations depend on it
    assert!(
        impact.is_empty(),
        "sorry axiom with no dependents should have empty impact"
    );

    // Should appear in priority list
    assert!(
        tracer
            .priority()
            .iter()
            .any(|(n, _)| n.to_string() == "my_sorry"),
        "my_sorry should appear in priority list"
    );
}

// ---- Test: definition depending on sorry axiom ----

#[test]
fn test_sorry_tracer_definition_depends_on_sorry() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "my_axiom", Expr::prop());

    // Add a definition whose value references the sorry axiom
    let axiom_ref = Expr::const_(Name::from_string("my_axiom"), vec![]);
    add_definition(&mut env, "my_def", Expr::prop(), axiom_ref);

    let tracer = SorryTracer::build(&env);

    // Forward: my_def depends on my_axiom
    let deps = tracer.trace_deps(&Name::from_string("my_def"));
    assert!(
        deps.iter().any(|n| n.to_string() == "my_axiom"),
        "my_def should depend on my_axiom"
    );

    // Reverse: my_axiom has my_def as dependent
    let impact = tracer.impact(&Name::from_string("my_axiom"));
    assert!(
        impact.iter().any(|n| n.to_string() == "my_def"),
        "my_axiom should have my_def as dependent"
    );
}

// ---- Test: chain dependencies (A -> B -> sorry) ----

#[test]
fn test_sorry_tracer_chain_dependency() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "base_sorry", Expr::prop());

    // mid_def depends on base_sorry
    let sorry_ref = Expr::const_(Name::from_string("base_sorry"), vec![]);
    add_definition(&mut env, "mid_def", Expr::prop(), sorry_ref);

    // top_def depends on mid_def (transitively on base_sorry)
    let mid_ref = Expr::const_(Name::from_string("mid_def"), vec![]);
    add_definition(&mut env, "top_def", Expr::prop(), mid_ref);

    let tracer = SorryTracer::build(&env);

    // top_def should transitively depend on base_sorry
    let deps = tracer.trace_deps(&Name::from_string("top_def"));
    assert!(
        deps.iter().any(|n| n.to_string() == "base_sorry"),
        "top_def should transitively depend on base_sorry"
    );

    // base_sorry should have both mid_def and top_def as dependents
    let impact = tracer.impact(&Name::from_string("base_sorry"));
    assert!(
        impact.iter().any(|n| n.to_string() == "mid_def"),
        "base_sorry should have mid_def as dependent"
    );
    assert!(
        impact.iter().any(|n| n.to_string() == "top_def"),
        "base_sorry should have top_def as dependent"
    );
}

// ---- Test: diamond dependencies (A -> B, A -> C, B -> sorry, C -> sorry) ----

#[test]
fn test_sorry_tracer_diamond_dependency() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "diamond_sorry", Expr::prop());

    // left and right both depend on diamond_sorry
    let sorry_ref = Expr::const_(Name::from_string("diamond_sorry"), vec![]);
    add_definition(&mut env, "left_def", Expr::prop(), sorry_ref.clone());
    add_definition(&mut env, "right_def", Expr::prop(), sorry_ref);

    // top depends on both left and right
    let left_ref = Expr::const_(Name::from_string("left_def"), vec![]);
    let right_ref = Expr::const_(Name::from_string("right_def"), vec![]);
    let both = Expr::app(left_ref, right_ref);
    add_definition(&mut env, "top_def", Expr::prop(), both);

    let tracer = SorryTracer::build(&env);

    // top_def should depend on diamond_sorry (only once in the list)
    let deps = tracer.trace_deps(&Name::from_string("top_def"));
    let sorry_count = deps
        .iter()
        .filter(|n| n.to_string() == "diamond_sorry")
        .count();
    assert_eq!(
        sorry_count, 1,
        "diamond sorry should appear exactly once in deps"
    );

    // diamond_sorry should have 3 dependents: left, right, top
    let impact = tracer.impact(&Name::from_string("diamond_sorry"));
    assert!(
        impact.len() >= 3,
        "diamond_sorry should have at least 3 dependents"
    );
}

// ---- Test: no sorry dependencies ----

#[test]
fn test_sorry_tracer_no_sorry_deps() {
    let mut env = fresh_env();

    // Add a definition that references nothing sorry-like
    add_definition(&mut env, "pure_def", Expr::prop(), Expr::prop());

    let tracer = SorryTracer::build(&env);
    let deps = tracer.trace_deps(&Name::from_string("pure_def"));
    assert!(
        deps.is_empty(),
        "definition with no sorry deps should have empty trace"
    );
    assert!(
        !tracer.has_sorry_deps(&Name::from_string("pure_def")),
        "has_sorry_deps should return false for pure definition"
    );
}

// ---- Test: priority ordering (most dependents first) ----

#[test]
fn test_sorry_tracer_priority_ordering() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "popular_sorry", Expr::prop());
    add_sorry_axiom(&mut env, "unpopular_sorry", Expr::prop());

    // 3 definitions depend on popular_sorry
    for i in 0..3 {
        let sorry_ref = Expr::const_(Name::from_string("popular_sorry"), vec![]);
        add_definition(
            &mut env,
            &format!("dep_popular_{i}"),
            Expr::prop(),
            sorry_ref,
        );
    }

    // 1 definition depends on unpopular_sorry
    let sorry_ref = Expr::const_(Name::from_string("unpopular_sorry"), vec![]);
    add_definition(&mut env, "dep_unpopular_0", Expr::prop(), sorry_ref);

    let tracer = SorryTracer::build(&env);
    let priority = tracer.priority();

    // Find positions
    let popular_pos = priority
        .iter()
        .position(|(n, _)| n.to_string() == "popular_sorry");
    let unpopular_pos = priority
        .iter()
        .position(|(n, _)| n.to_string() == "unpopular_sorry");

    assert!(
        popular_pos.is_some(),
        "popular_sorry should be in priority list"
    );
    assert!(
        unpopular_pos.is_some(),
        "unpopular_sorry should be in priority list"
    );

    // popular_sorry should come before unpopular_sorry (lower index = higher priority)
    assert!(
        popular_pos.unwrap() < unpopular_pos.unwrap(),
        "popular_sorry ({} deps) should rank higher than unpopular_sorry ({} deps)",
        priority[popular_pos.unwrap()].1,
        priority[unpopular_pos.unwrap()].1
    );
}

// ---- Test: sorry_count ----

#[test]
fn test_sorry_tracer_sorry_count() {
    let mut env = fresh_env();
    let initial_tracer = SorryTracer::build(&env);
    let initial_count = initial_tracer.sorry_count();

    add_sorry_axiom(&mut env, "sorry_a", Expr::prop());
    add_sorry_axiom(&mut env, "sorry_b", Expr::prop());

    let tracer = SorryTracer::build(&env);
    assert_eq!(
        tracer.sorry_count(),
        initial_count + 2,
        "sorry_count should reflect added sorry axioms"
    );
}

// ---- Test: has_sorry_deps ----

#[test]
fn test_sorry_tracer_has_sorry_deps() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "my_sorry", Expr::prop());

    let sorry_ref = Expr::const_(Name::from_string("my_sorry"), vec![]);
    add_definition(&mut env, "uses_sorry", Expr::prop(), sorry_ref);
    add_definition(&mut env, "pure", Expr::prop(), Expr::prop());

    let tracer = SorryTracer::build(&env);
    assert!(tracer.has_sorry_deps(&Name::from_string("uses_sorry")));
    assert!(!tracer.has_sorry_deps(&Name::from_string("pure")));
}

// ---- Test: theorem depending on sorry ----

#[test]
fn test_sorry_tracer_theorem_depends_on_sorry() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "thm_sorry", Expr::prop());

    let sorry_ref = Expr::const_(Name::from_string("thm_sorry"), vec![]);
    add_theorem(&mut env, "my_thm", Expr::prop(), sorry_ref);

    let tracer = SorryTracer::build(&env);
    let deps = tracer.trace_deps(&Name::from_string("my_thm"));
    assert!(
        deps.iter().any(|n| n.to_string() == "thm_sorry"),
        "theorem should show sorry dependency"
    );
}

// ---- Test: multiple sorry axioms in one declaration ----

#[test]
fn test_sorry_tracer_multiple_sorry_in_one_decl() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "sorry_x", Expr::prop());
    add_sorry_axiom(&mut env, "sorry_y", Expr::prop());

    // Definition references both sorry axioms
    let ref_x = Expr::const_(Name::from_string("sorry_x"), vec![]);
    let ref_y = Expr::const_(Name::from_string("sorry_y"), vec![]);
    let both = Expr::app(ref_x, ref_y);
    add_definition(&mut env, "multi_sorry_def", Expr::prop(), both);

    let tracer = SorryTracer::build(&env);
    let deps = tracer.trace_deps(&Name::from_string("multi_sorry_def"));
    assert!(
        deps.iter().any(|n| n.to_string() == "sorry_x"),
        "should depend on sorry_x"
    );
    assert!(
        deps.iter().any(|n| n.to_string() == "sorry_y"),
        "should depend on sorry_y"
    );
    assert_eq!(deps.len(), 2, "should depend on exactly 2 sorry axioms");
}

// ---- Test: convenience methods on Environment ----

#[test]
fn test_env_trace_sorry_deps() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "env_sorry", Expr::prop());

    let sorry_ref = Expr::const_(Name::from_string("env_sorry"), vec![]);
    add_definition(&mut env, "env_def", Expr::prop(), sorry_ref);

    let deps = env.trace_sorry_deps(&Name::from_string("env_def"));
    assert!(deps.iter().any(|n| n.to_string() == "env_sorry"));
}

#[test]
fn test_env_sorry_impact() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "impact_sorry", Expr::prop());

    let sorry_ref = Expr::const_(Name::from_string("impact_sorry"), vec![]);
    add_definition(&mut env, "impact_def", Expr::prop(), sorry_ref);

    let impact = env.sorry_impact(&Name::from_string("impact_sorry"));
    assert!(impact.iter().any(|n| n.to_string() == "impact_def"));
}

#[test]
fn test_env_sorry_priority() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "prio_sorry", Expr::prop());

    let sorry_ref = Expr::const_(Name::from_string("prio_sorry"), vec![]);
    add_definition(&mut env, "prio_def", Expr::prop(), sorry_ref);

    let priority = env.sorry_priority();
    assert!(
        priority
            .iter()
            .any(|(n, count)| n.to_string() == "prio_sorry" && *count >= 1),
        "prio_sorry should appear in priority list with >= 1 dependent"
    );
}

// ---- Test: nonexistent declaration ----

#[test]
fn test_sorry_tracer_nonexistent_decl() {
    let env = fresh_env();
    let tracer = SorryTracer::build(&env);
    let deps = tracer.trace_deps(&Name::from_string("does_not_exist"));
    assert!(deps.is_empty(), "nonexistent decl should have empty deps");
}

// ---- Test: sorry axiom itself has no forward deps (unless it refs another sorry) ----

#[test]
fn test_sorry_tracer_sorry_axiom_self_deps() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "standalone_sorry", Expr::prop());

    let tracer = SorryTracer::build(&env);
    // A sorry axiom with type `Prop` doesn't reference other sorry axioms
    let deps = tracer.trace_deps(&Name::from_string("standalone_sorry"));
    assert!(
        deps.is_empty(),
        "standalone sorry axiom should not depend on other sorry axioms"
    );
}

// ---- Test: deep chain (5 levels deep) ----

#[test]
fn test_sorry_tracer_deep_chain() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "deep_sorry", Expr::prop());

    let mut prev_name = "deep_sorry".to_string();
    for i in 0..5 {
        let prev_ref = Expr::const_(Name::from_string(&prev_name), vec![]);
        let new_name = format!("chain_{i}");
        add_definition(&mut env, &new_name, Expr::prop(), prev_ref);
        prev_name = new_name;
    }

    let tracer = SorryTracer::build(&env);
    // The last in the chain should transitively depend on deep_sorry
    let deps = tracer.trace_deps(&Name::from_string("chain_4"));
    assert!(
        deps.iter().any(|n| n.to_string() == "deep_sorry"),
        "chain_4 should transitively depend on deep_sorry through 5 levels"
    );

    // deep_sorry should have all 5 chain declarations as dependents
    let impact = tracer.impact(&Name::from_string("deep_sorry"));
    for i in 0..5 {
        let chain_name = format!("chain_{i}");
        assert!(
            impact.iter().any(|n| n.to_string() == chain_name),
            "deep_sorry should have {chain_name} as dependent"
        );
    }
}

// ---- Test: type-level sorry dependency ----

#[test]
fn test_sorry_tracer_type_level_dependency() {
    let mut env = fresh_env();
    add_sorry_axiom(&mut env, "type_sorry", Expr::prop());

    // Definition whose TYPE (not value) references the sorry axiom
    let sorry_type = Expr::const_(Name::from_string("type_sorry"), vec![]);
    add_definition(&mut env, "typed_def", sorry_type, Expr::prop());

    let tracer = SorryTracer::build(&env);
    let deps = tracer.trace_deps(&Name::from_string("typed_def"));
    assert!(
        deps.iter().any(|n| n.to_string() == "type_sorry"),
        "type-level sorry reference should be detected"
    );
}

// ---- Drift regression (#3560 / #3573) ----

/// `sorry_tracer` and `axiom_audit` must agree on the foundational
/// whitelist. Prior to #3560 `sorry_tracer.rs` carried its own hard-coded
/// copy (`is_foundational_axiom_name`) which drifted from the canonical
/// `axiom_audit::FOUNDATIONAL_AXIOMS` list — missing Rat min/max, the Fin
/// family, the Rat ring batches (#3551), the Rat field axioms (#3555), and
/// `Nat.le_refl`. The two classifications then diverged, so the sorry
/// tracer reported names that `proof_quality()` considered foundational
/// as sorry obligations.
///
/// This test drives every entry of the canonical `FOUNDATIONAL_AXIOMS`
/// table at runtime rather than pinning a hand-maintained copy, so the
/// single-source-of-truth invariant survives whitelist edits (e.g., the
/// #3559 trim that demoted `Rat.add_le_add`, `Rat.neg_le_neg`, `Eq.symm`,
/// `Eq.trans`, and `Eq.subst` to kernel-checked theorems). If the single
/// predicate is ever split again, this test will catch it.
///
/// #integrity-audit (2026-06): The ~38 admitted DOMAIN axioms (the Rat
/// ordered-field / lattice, `Fin.castSucc` / `Fin.last`, and the Nat
/// bitwise primitives — see `ADMITTED_DOMAIN_AXIOMS`) were dishonestly
/// whitelisted as "foundational" for ergonomic kernel use (#3490 / #3543 /
/// #3551 / #3555), so theorems resting on them were overstated as
/// `ProofQuality::Constructive`. They are mathematically true but UNPROVED
/// in this kernel, so they are now EXCLUDED from `is_foundational_axiom`
/// even though they remain physically present in the `FOUNDATIONAL_AXIOMS`
/// slice (kept only to preserve the disjointness / documentation
/// invariants). The single-source-of-truth invariant is therefore now:
/// `is_sorry_axiom` and `is_foundational_axiom` must AGREE on every entry,
/// with the admitted-domain entries honestly classified as sorry
/// obligations (non-foundational) and the genuine logical foundations
/// classified as foundational (non-sorry).
#[test]
fn test_sorry_tracer_uses_canonical_foundational_whitelist() {
    assert!(
        !FOUNDATIONAL_AXIOMS.is_empty(),
        "FOUNDATIONAL_AXIOMS must not be empty — the canonical whitelist is the \
         single source of truth for foundational classification"
    );

    // The genuine logical foundations: every FOUNDATIONAL_AXIOMS entry that
    // is NOT an admitted domain axiom must remain truly foundational.
    let genuine_foundations: Vec<&str> = FOUNDATIONAL_AXIOMS
        .iter()
        .copied()
        .filter(|n| !ADMITTED_DOMAIN_AXIOMS.contains(n))
        .collect();
    assert!(
        !genuine_foundations.is_empty(),
        "after excluding admitted domain axioms there must still be genuine \
         logical-foundation axioms (propext, Quot.sound, Eq.refl, …) in the \
         whitelist"
    );

    for &name in FOUNDATIONAL_AXIOMS {
        let n = Name::from_string(name);
        let info = synth_axiom_info(name);
        let is_admitted = ADMITTED_DOMAIN_AXIOMS.contains(&name);

        if is_admitted {
            // #integrity-audit: admitted DOMAIN axioms are mathematically
            // true but unproved in THIS kernel — they are NOT foundational,
            // and the sorry tracer must honestly surface them as sorry
            // obligations (the trust gap) rather than masking them.
            assert!(
                !is_foundational_axiom(&n),
                "{name} is an admitted DOMAIN axiom (in ADMITTED_DOMAIN_AXIOMS) and \
                 must NOT be classified as foundational — it is unproved in this \
                 kernel (#integrity-audit)"
            );
            assert!(
                is_sorry_axiom(&info),
                "{name} is an admitted DOMAIN axiom and must be classified as a \
                 sorry obligation by the tracer — both predicates must agree on \
                 the honest non-foundational state (#integrity-audit)"
            );
        } else {
            // Genuine logical foundation — axiom_audit is the source of
            // truth and the public predicate must agree with the table.
            assert!(
                is_foundational_axiom(&n),
                "{name} must be classified as foundational by is_foundational_axiom \
                 (genuine logical foundation present in FOUNDATIONAL_AXIOMS but \
                 predicate disagrees)"
            );

            // Drive the tracer's classifier through a synthetic axiom with
            // this exact name and confirm it is NOT a sorry obligation. If
            // the sorry tracer ever re-acquires a hard-coded copy of the
            // whitelist, any new entry added to FOUNDATIONAL_AXIOMS will
            // silently fail this check (drift regression #3560 / #3573).
            assert!(
                !is_sorry_axiom(&info),
                "{name} is foundational per axiom_audit but sorry_tracer \
                 classifies it as a sorry obligation — drift regression \
                 (#3560 / #3573)"
            );
        }
    }
}

/// Negative form of the drift regression: known sorry / trust-marker /
/// domain-specific names must still be classified as sorry obligations.
#[test]
fn test_sorry_tracer_non_foundational_still_sorry() {
    // Names that must be sorry obligations (NOT foundational).
    let non_foundational = [
        "sorryAx",        // trust marker, moved out of FOUNDATIONAL_AXIOMS in #3554
        "trustedArith",   // trust marker
        "trustedAy",      // trust marker
        "my_domain_goal", // arbitrary domain axiom
    ];

    for name in non_foundational {
        let info = synth_axiom_info(name);
        assert!(
            is_sorry_axiom(&info),
            "{name} must be classified as a sorry obligation by the tracer"
        );
    }
}
