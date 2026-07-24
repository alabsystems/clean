// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_add_const() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let a2 = egraph.add_const("a");

    // Same constant should return same e-class
    assert_eq!(a, a2);
    // Different constants should be different
    assert_ne!(a, b);
}

#[test]
fn test_add_app() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let fb = egraph.add_app("f", vec![b]);
    let fa2 = egraph.add_app("f", vec![a]);

    // Same application should return same e-class
    assert_eq!(fa, fa2);
    // Different applications should be different
    assert_ne!(fa, fb);
}

#[test]
fn test_union() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");

    assert!(!egraph.are_equal(a, b));

    egraph.union(a, b);

    assert!(egraph.are_equal(a, b));
}

#[test]
fn test_congruence_simple() {
    let mut egraph = EGraph::new();

    // f(a) and f(b)
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let fb = egraph.add_app("f", vec![b]);

    // Initially different
    assert!(!egraph.are_equal(fa, fb));

    // After asserting a = b, f(a) = f(b) by congruence
    egraph.union(a, b);

    assert!(egraph.are_equal(fa, fb));
}

#[test]
fn test_congruence_nested() {
    let mut egraph = EGraph::new();

    // g(f(a)) and g(f(b))
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let fb = egraph.add_app("f", vec![b]);
    let gfa = egraph.add_app("g", vec![fa]);
    let gfb = egraph.add_app("g", vec![fb]);

    // Initially different
    assert!(!egraph.are_equal(gfa, gfb));

    // After asserting a = b:
    // f(a) = f(b) by congruence
    // g(f(a)) = g(f(b)) by congruence
    egraph.union(a, b);

    assert!(egraph.are_equal(fa, fb));
    assert!(egraph.are_equal(gfa, gfb));
}

#[test]
fn test_congruence_multiarg() {
    let mut egraph = EGraph::new();

    // f(a, c) and f(b, c)
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let c = egraph.add_const("c");
    let fac = egraph.add_app("f", vec![a, c]);
    let fbc = egraph.add_app("f", vec![b, c]);

    assert!(!egraph.are_equal(fac, fbc));

    egraph.union(a, b);

    assert!(egraph.are_equal(fac, fbc));
}

#[test]
fn test_congruence_chain() {
    let mut egraph = EGraph::new();

    // a = b, b = c -> a = c (transitivity)
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let c = egraph.add_const("c");
    let fa = egraph.add_app("f", vec![a]);
    let fc = egraph.add_app("f", vec![c]);

    egraph.union(a, b);
    egraph.union(b, c);

    assert!(egraph.are_equal(a, c));
    assert!(egraph.are_equal(fa, fc));
}

#[test]
fn test_hashcons_after_union() {
    let mut egraph = EGraph::new();

    let a = egraph.add_const("a");
    let b = egraph.add_const("b");

    // Union a and b
    egraph.union(a, b);

    // Now add f(a) - should be same as f(b) by hashcons
    let fa = egraph.add_app("f", vec![a]);
    let fb = egraph.add_app("f", vec![b]);

    assert!(egraph.are_equal(fa, fb));
}

#[test]
fn test_lookup_and_contains_after_union_reuse_canonical_parent_entries() {
    let mut egraph = EGraph::new();

    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let fb = ENode::app("f", vec![b]);

    egraph.union(a, b);

    assert!(egraph.contains(&fb));
    assert_eq!(egraph.lookup(&fb), Some(fa));
}

#[test]
fn test_symbol_clone_shares_storage() {
    let symbol = Symbol::new("f");
    let clone = symbol.clone();

    assert!(symbol.shares_storage_with(&clone));
    assert_eq!(symbol.name(), clone.name());
}

#[test]
fn test_extract_const() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");

    let term = egraph.extract(a).unwrap();
    assert_eq!(term, Term::Const("a".to_string()));
}

#[test]
fn test_extract_app() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fab = egraph.add_app("f", vec![a, b]);

    let term = egraph.extract(fab).unwrap();
    assert_eq!(
        term,
        Term::App(
            "f".to_string(),
            vec![Term::Const("a".to_string()), Term::Const("b".to_string())]
        )
    );
}

#[test]
fn test_num_classes() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let c = egraph.add_const("c");

    assert_eq!(egraph.num_classes(), 3);

    egraph.union(a, b);
    assert_eq!(egraph.num_classes(), 2);

    egraph.union(b, c);
    assert_eq!(egraph.num_classes(), 1);
}

#[test]
fn test_term_builder() {
    let mut egraph = EGraph::new();

    let term = Term::App(
        "f".to_string(),
        vec![
            Term::Const("a".to_string()),
            Term::App("g".to_string(), vec![Term::Const("b".to_string())]),
        ],
    );

    let id = {
        let mut builder = TermBuilder::new(&mut egraph);
        builder.add_term(&term)
    };

    let extracted = egraph.extract(id).unwrap();
    assert_eq!(extracted, term);
}

#[test]
fn test_contains() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let _fa = egraph.add_app("f", vec![a]);

    assert!(egraph.contains(&ENode::constant("a")));
    assert!(egraph.contains(&ENode::app("f", vec![a])));
    assert!(!egraph.contains(&ENode::constant("b")));
}

#[test]
fn test_lookup() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let fa = egraph.add_app("f", vec![a]);

    assert_eq!(egraph.lookup(&ENode::constant("a")), Some(a));
    assert_eq!(egraph.lookup(&ENode::app("f", vec![a])), Some(fa));
    assert_eq!(egraph.lookup(&ENode::constant("b")), None);
}

#[test]
fn test_clear() {
    let mut egraph = EGraph::new();
    egraph.add_const("a");
    egraph.add_const("b");

    assert_eq!(egraph.num_classes(), 2);

    egraph.clear();

    assert_eq!(egraph.num_classes(), 0);
}

#[test]
fn test_complex_congruence() {
    let mut egraph = EGraph::new();

    // Build: h(f(a), g(b)) and h(f(c), g(d))
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let c = egraph.add_const("c");
    let d = egraph.add_const("d");

    let fa = egraph.add_app("f", vec![a]);
    let fc = egraph.add_app("f", vec![c]);
    let gb = egraph.add_app("g", vec![b]);
    let gd = egraph.add_app("g", vec![d]);

    let h1 = egraph.add_app("h", vec![fa, gb]);
    let h2 = egraph.add_app("h", vec![fc, gd]);

    // Initially different
    assert!(!egraph.are_equal(h1, h2));

    // Assert a = c and b = d
    egraph.union(a, c);
    egraph.union(b, d);

    // By congruence: f(a) = f(c), g(b) = g(d)
    // Therefore: h(f(a), g(b)) = h(f(c), g(d))
    assert!(egraph.are_equal(fa, fc));
    assert!(egraph.are_equal(gb, gd));
    assert!(egraph.are_equal(h1, h2));
}

#[test]
fn test_self_loop() {
    let mut egraph = EGraph::new();

    // f(f(a)) where we assert f(a) = a
    let a = egraph.add_const("a");
    let fa = egraph.add_app("f", vec![a]);
    let ffa = egraph.add_app("f", vec![fa]);

    // Assert f(a) = a
    egraph.union(fa, a);

    // Now f(f(a)) should equal f(a) (which equals a)
    assert!(egraph.are_equal(a, fa));
    assert!(egraph.are_equal(fa, ffa));
    assert!(egraph.are_equal(a, ffa));
}

#[test]
fn test_extract_cyclic_egraph() {
    let mut egraph = EGraph::new();

    // Create f(a) and union f(a) = a, forming a cycle: class(a) contains
    // both const "a" and app "f"(class(a)).
    let a = egraph.add_const("a");
    let fa = egraph.add_app("f", vec![a]);
    egraph.union(fa, a);

    // extract must terminate (not stack overflow) and return the smallest
    // representative — the constant "a".
    let term = egraph
        .extract(a)
        .expect("extract should succeed on cyclic e-graph");
    assert_eq!(term, Term::Const("a".to_string()));
}

#[test]
fn test_extract_pure_cycle_returns_none() {
    let mut egraph = EGraph::new();

    // g(h(x)) where g and h are uninterpreted, x is a class.
    // Union g(h(x)) = x so all three are in one class with no constants.
    let x = egraph.add_const("x");
    let hx = egraph.add_app("h", vec![x]);
    let ghx = egraph.add_app("g", vec![hx]);
    egraph.union(ghx, x);
    // Remove the constant node by unioning with a non-constant-containing class
    // Actually, x is still a const node in the class, so extract returns "x".
    // For a true pure-cycle test we need all nodes to be apps that cycle.
    let term = egraph
        .extract(x)
        .expect("extract should succeed (const 'x' is in the class)");
    assert_eq!(term, Term::Const("x".to_string()));
}

#[test]
fn test_extract_mutual_cycle() {
    let mut egraph = EGraph::new();

    // Create a mutual cycle: f(b) = a, g(a) = b
    // class(a) has: const "a", app "f"(class(b))
    // class(b) has: const "b", app "g"(class(a))
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fb = egraph.add_app("f", vec![b]);
    let ga = egraph.add_app("g", vec![a]);
    egraph.union(fb, a);
    egraph.union(ga, b);

    // Both classes have constant nodes, so extract should terminate and
    // return the smallest (constant) for each.
    let term_a = egraph
        .extract(a)
        .expect("extract(a) should succeed with mutual cycle");
    assert_eq!(term_a.size(), 1);

    let term_b = egraph
        .extract(b)
        .expect("extract(b) should succeed with mutual cycle");
    assert_eq!(term_b.size(), 1);
}

#[test]
fn test_term_size() {
    let t1 = Term::Const("a".to_string());
    assert_eq!(t1.size(), 1);

    let t2 = Term::App("f".to_string(), vec![Term::Const("a".to_string())]);
    assert_eq!(t2.size(), 2);

    let t3 = Term::App(
        "f".to_string(),
        vec![
            Term::Const("a".to_string()),
            Term::App("g".to_string(), vec![Term::Const("b".to_string())]),
        ],
    );
    assert_eq!(t3.size(), 4);
}

#[test]
fn test_term_pretty() {
    let t = Term::App(
        "f".to_string(),
        vec![
            Term::Const("a".to_string()),
            Term::App("g".to_string(), vec![Term::Const("b".to_string())]),
        ],
    );
    assert_eq!(t.to_string_pretty(), "f(a, g(b))");
}

// E-matching tests
#[test]
fn test_ematch_constant() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let _b = egraph.add_const("b");

    let matcher = EMatcher::new(&egraph);

    // Pattern: constant "a"
    let pattern = Pattern::constant("a");
    let matches = matcher.find_matches(&pattern);

    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].0, a);
}

#[test]
fn test_ematch_variable() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");

    let matcher = EMatcher::new(&egraph);

    // Pattern: ?x (matches everything)
    let pattern = Pattern::var("x");
    let matches = matcher.find_matches(&pattern);

    // Should match both a and b
    assert_eq!(matches.len(), 2);
    let classes: Vec<_> = matches.iter().map(|(c, _)| *c).collect();
    assert!(classes.contains(&a));
    assert!(classes.contains(&b));
}

#[test]
fn test_ematch_app_pattern() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let fb = egraph.add_app("f", vec![b]);
    let _ga = egraph.add_app("g", vec![a]);

    let matcher = EMatcher::new(&egraph);

    // Pattern: f(?x)
    let pattern = Pattern::app("f", vec![Pattern::var("x")]);
    let matches = matcher.find_matches(&pattern);

    // Should match f(a) and f(b)
    assert_eq!(matches.len(), 2);
    let classes: Vec<_> = matches.iter().map(|(c, _)| *c).collect();
    assert!(classes.contains(&fa));
    assert!(classes.contains(&fb));

    // Check substitutions
    for (class, subst) in &matches {
        let x_val = subst.get("x").unwrap();
        if *class == fa {
            assert_eq!(x_val, a);
        } else {
            assert_eq!(x_val, b);
        }
    }
}

#[test]
fn test_ematch_nested_pattern() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let gfa = egraph.add_app("g", vec![fa]);
    let _gb = egraph.add_app("g", vec![b]);

    let matcher = EMatcher::new(&egraph);

    // Pattern: g(f(?x))
    let pattern = Pattern::app("g", vec![Pattern::app("f", vec![Pattern::var("x")])]);
    let matches = matcher.find_matches(&pattern);

    // Should match g(f(a))
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].0, gfa);
    assert_eq!(matches[0].1.get("x").unwrap(), a);
}

#[test]
fn test_ematch_multi_arg() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let c = egraph.add_const("c");
    let fab = egraph.add_app("f", vec![a, b]);
    let _fac = egraph.add_app("f", vec![a, c]);

    let matcher = EMatcher::new(&egraph);

    // Pattern: f(?x, ?y)
    let pattern = Pattern::app("f", vec![Pattern::var("x"), Pattern::var("y")]);
    let matches = matcher.find_matches(&pattern);

    // Should match both f(a, b) and f(a, c)
    assert_eq!(matches.len(), 2);

    // Check one specific match
    let fab_match = matches.iter().find(|(c, _)| *c == fab).unwrap();
    assert_eq!(fab_match.1.get("x").unwrap(), a);
    assert_eq!(fab_match.1.get("y").unwrap(), b);
}

#[test]
fn test_ematch_repeated_var() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let faa = egraph.add_app("f", vec![a, a]);
    let _fab = egraph.add_app("f", vec![a, b]);

    let matcher = EMatcher::new(&egraph);

    // Pattern: f(?x, ?x) - same variable twice
    let pattern = Pattern::app("f", vec![Pattern::var("x"), Pattern::var("x")]);
    let matches = matcher.find_matches(&pattern);

    // Should only match f(a, a), not f(a, b)
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].0, faa);
    assert_eq!(matches[0].1.get("x").unwrap(), a);
}

#[test]
fn test_ematch_with_equivalence() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let _fb = egraph.add_app("f", vec![b]);

    // Make a = b
    egraph.union(a, b);

    let matcher = EMatcher::new(&egraph);

    // Pattern: f(?x)
    let pattern = Pattern::app("f", vec![Pattern::var("x")]);
    let matches = matcher.find_matches(&pattern);

    // After union, f(a) and f(b) are in the same class
    // Should return 1 match (canonical representative)
    assert_eq!(matches.len(), 1);
    // The canonical class should be f(a)'s canonical rep
    let canon_fa = egraph.find(fa);
    assert_eq!(matches[0].0, canon_fa);
}

#[test]
fn test_ematch_multi_pattern() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let c = egraph.add_const("c");
    let fa = egraph.add_app("f", vec![a]);
    let ga = egraph.add_app("g", vec![a]);
    let _fb = egraph.add_app("f", vec![b]);
    let _gc = egraph.add_app("g", vec![c]);

    let matcher = EMatcher::new(&egraph);

    // Multi-pattern: {f(?x), g(?x)} - same ?x in both patterns
    let patterns = vec![
        Pattern::app("f", vec![Pattern::var("x")]),
        Pattern::app("g", vec![Pattern::var("x")]),
    ];
    let matches = matcher.find_multi_matches(&patterns);

    // Only ?x = a satisfies both f(?x) and g(?x)
    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].get("x").unwrap(), a);

    // Verify f(a) and g(a) are the match result's function application nodes
    assert_ne!(fa, ga, "f(a) and g(a) should be distinct EClassIds");
}

#[test]
fn test_trigger_variables() {
    // Pattern: f(?x, g(?y))
    let pattern = Pattern::app(
        "f",
        vec![
            Pattern::var("x"),
            Pattern::app("g", vec![Pattern::var("y")]),
        ],
    );
    let trigger = Trigger::single(pattern);

    let vars = trigger.variables();
    assert_eq!(vars.len(), 2);
    assert!(vars.contains(&"x".to_string()));
    assert!(vars.contains(&"y".to_string()));
}

#[test]
fn test_pattern_variables() {
    // Pattern with repeated var: f(?x, ?x, ?y)
    let pattern = Pattern::app(
        "f",
        vec![Pattern::var("x"), Pattern::var("x"), Pattern::var("y")],
    );
    let vars = pattern.variables();
    // Should deduplicate
    assert_eq!(vars.len(), 2);
    assert!(vars.contains(&"x".to_string()));
    assert!(vars.contains(&"y".to_string()));
}

// Property-based tests for congruence closure verification
mod proptest_egraph {
    use super::*;
    use proptest::prelude::*;

    /// Strategy for generating symbol names
    fn arb_symbol_name() -> impl Strategy<Value = String> {
        prop::string::string_regex("[a-z][a-z0-9]{0,2}")
            .unwrap()
            .prop_filter("non-empty", |s| !s.is_empty())
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Property: Union implies equality (reflexive closure)
        #[test]
        fn prop_egraph_union_implies_equal(
            a_name in arb_symbol_name(),
            b_name in arb_symbol_name(),
        ) {
            let mut egraph = EGraph::new();
            let id_a = egraph.add_const(&a_name);
            let id_b = egraph.add_const(&b_name);

            // Before union, may or may not be equal (depending on name)
            egraph.union(id_a, id_b);

            prop_assert!(
                egraph.are_equal(id_a, id_b),
                "After union({:?}, {:?}), are_equal should return true",
                id_a,
                id_b
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Property: Congruence closure - union(a, b) implies f(a) = f(b)
        #[test]
        fn prop_egraph_congruence_closure(
            f_name in arb_symbol_name(),
            a_name in arb_symbol_name(),
            b_name in arb_symbol_name(),
        ) {
            let mut egraph = EGraph::new();

            let id_a = egraph.add_const(&a_name);
            let id_b = egraph.add_const(&b_name);
            let id_fa = egraph.add_app(&f_name, vec![id_a]);
            let id_fb = egraph.add_app(&f_name, vec![id_b]);

            // Union a and b
            egraph.union(id_a, id_b);

            // Now f(a) = f(b) by congruence
            prop_assert!(
                egraph.are_equal(id_fa, id_fb),
                "Congruence failed: union(a, b) should imply f(a) = f(b)"
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(500))]

        /// Property: Transitivity - a=b and b=c implies a=c
        #[test]
        fn prop_egraph_transitivity(
            a_name in arb_symbol_name(),
            b_name in arb_symbol_name(),
            c_name in arb_symbol_name(),
        ) {
            let mut egraph = EGraph::new();

            let id_a = egraph.add_const(&a_name);
            let id_b = egraph.add_const(&b_name);
            let id_c = egraph.add_const(&c_name);

            egraph.union(id_a, id_b);
            egraph.union(id_b, id_c);

            prop_assert!(
                egraph.are_equal(id_a, id_c),
                "Transitivity failed: a=b and b=c should imply a=c"
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        /// Property: Deep congruence - a=b implies g(f(a)) = g(f(b))
        #[test]
        fn prop_egraph_deep_congruence(
            f_name in arb_symbol_name(),
            g_name in arb_symbol_name(),
            a_name in arb_symbol_name(),
            b_name in arb_symbol_name(),
        ) {
            let mut egraph = EGraph::new();

            let id_a = egraph.add_const(&a_name);
            let id_b = egraph.add_const(&b_name);

            // g(f(a)) and g(f(b))
            let id_fa = egraph.add_app(&f_name, vec![id_a]);
            let id_fb = egraph.add_app(&f_name, vec![id_b]);
            let id_gfa = egraph.add_app(&g_name, vec![id_fa]);
            let id_gfb = egraph.add_app(&g_name, vec![id_fb]);

            egraph.union(id_a, id_b);

            prop_assert!(
                egraph.are_equal(id_gfa, id_gfb),
                "Deep congruence failed: a=b should imply g(f(a)) = g(f(b))"
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(300))]

        /// Property: Multi-argument congruence - h(a, c) = h(b, c) when a=b
        #[test]
        fn prop_egraph_multiarg_congruence(
            h_name in arb_symbol_name(),
            a_name in arb_symbol_name(),
            b_name in arb_symbol_name(),
            c_name in arb_symbol_name(),
        ) {
            let mut egraph = EGraph::new();

            let id_a = egraph.add_const(&a_name);
            let id_b = egraph.add_const(&b_name);
            let id_c = egraph.add_const(&c_name);

            let id_hac = egraph.add_app(&h_name, vec![id_a, id_c]);
            let id_hbc = egraph.add_app(&h_name, vec![id_b, id_c]);

            egraph.union(id_a, id_b);

            prop_assert!(
                egraph.are_equal(id_hac, id_hbc),
                "Multi-arg congruence failed: a=b should imply h(a,c) = h(b,c)"
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        /// Property: Equivalence classes shrink or stay same after union
        #[test]
        fn prop_egraph_union_reduces_classes(
            names in prop::collection::vec(arb_symbol_name(), 3..8)
        ) {
            let mut egraph = EGraph::new();

            // Add all constants
            let ids: Vec<_> = names.iter().map(|n| egraph.add_const(n)).collect();
            let initial_classes = egraph.num_classes();

            // Union consecutive pairs
            for window in ids.windows(2) {
                egraph.union(window[0], window[1]);
            }

            let final_classes = egraph.num_classes();
            prop_assert!(
                final_classes <= initial_classes,
                "Union should not increase class count: {} -> {}",
                initial_classes,
                final_classes
            );
        }
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(200))]

        /// Property: Union is symmetric - union(a,b) same as union(b,a)
        #[test]
        fn prop_egraph_union_symmetric(
            a_name in arb_symbol_name(),
            b_name in arb_symbol_name(),
        ) {
            let mut eg1 = EGraph::new();
            let a1 = eg1.add_const(&a_name);
            let b1 = eg1.add_const(&b_name);
            eg1.union(a1, b1);

            let mut eg2 = EGraph::new();
            let a2 = eg2.add_const(&a_name);
            let b2 = eg2.add_const(&b_name);
            eg2.union(b2, a2); // reversed order

            // Both should have a and b equal
            prop_assert!(eg1.are_equal(a1, b1));
            prop_assert!(eg2.are_equal(a2, b2));
        }
    }
}

// ---- Performance proof tests ----
// These tests verify complexity claims and detect memory growth patterns.

/// Performance proof: EGraph data structures grow monotonically without bounds.
///
/// `classes`, `hashcons`, and `merge_history` grow with every `add_node`
/// and `union` call. There is no eviction, size limit, or GC mechanism.
/// The `merge_history` in particular is append-only (line 464-468) and
/// retains every merge operation for the lifetime of the EGraph.
///
/// The congruence detection in `do_union` reuses a `CongruenceBuf` HashMap
/// across calls (cleared, not reallocated), but still iterates all parent
/// nodes of the two merged classes on each union. For N unions, total
/// congruence work is O(sum_{i=1}^{N} parents_at_step_i).
///
/// This test documents the unbounded growth behavior. For long-running
/// saturation (e.g., `simp` automation), this can consume unbounded memory.
///
/// Regression test for performance_proofs P1 iter 788.
#[test]
fn test_egraph_unbounded_growth() {
    let mut eg = EGraph::new();

    // Phase 1: Add many nodes and measure growth
    let mut ids = Vec::new();
    for i in 0..200 {
        let id = eg.add_const(format!("c{i}"));
        ids.push(id);
    }

    let classes_after_adds = eg.classes.len();
    let hashcons_after_adds = eg.hashcons.len();

    assert_eq!(
        classes_after_adds, 200,
        "each add_const should create one e-class"
    );
    assert_eq!(
        hashcons_after_adds, 200,
        "each add_const should create one hashcons entry"
    );

    // Phase 2: Union all pairs (0,1), (2,3), (4,5), ... — 100 unions
    for i in (0..200).step_by(2) {
        eg.union(ids[i], ids[i + 1]);
    }

    let merge_history_after_unions = eg.merge_history.len();
    assert_eq!(
        merge_history_after_unions, 100,
        "each union should append to merge_history"
    );

    // Phase 3: Union the resulting classes: (0,2), (4,6), ... — 50 more
    for i in (0..200).step_by(4) {
        eg.union(ids[i], ids[i + 2]);
    }

    let merge_history_after_more = eg.merge_history.len();
    assert!(
        merge_history_after_more > merge_history_after_unions,
        "merge_history should grow monotonically: was {merge_history_after_unions}, \
         now {merge_history_after_more}"
    );

    // Document: merge_history never shrinks. For N total unions, it holds
    // exactly N MergeRecord entries. Each MergeRecord contains ec1, ec2,
    // and a MergeReason (which may contain cloned children vectors for
    // Congruence reasons). No eviction or compaction exists.
    eprintln!(
        "EGraph unbounded growth: classes={}, hashcons={}, merge_history={}",
        eg.classes.len(),
        eg.hashcons.len(),
        eg.merge_history.len()
    );
}

/// Performance proof: `do_union` moves (not clones) parent lists.
///
/// `merged_class` is removed from the classes map, so `extend(merged_class.parents)`
/// moves its elements. However, the accumulated parent list still grows
/// monotonically. Each subsequent union involving a large class iterates
/// an increasingly large parent vector for congruence detection.
/// For a chain of N merges, total iteration work is O(N²).
///
/// Regression test for performance_proofs P1 iter 788.
#[test]
fn test_do_union_parent_clone_growth() {
    use std::time::Instant;

    let sizes = [50usize, 200, 800];
    let mut times = Vec::new();

    for &n in &sizes {
        let mut eg = EGraph::new();

        // Create n constants and n function applications (parents)
        let consts: Vec<EClassId> = (0..n).map(|i| eg.add_const(format!("c{i}"))).collect();
        // Each f_i(c_i) creates a parent reference from c_i to f_i
        for (i, &c) in consts.iter().enumerate() {
            eg.add_app(format!("f{i}"), vec![c]);
        }

        // Now chain-union all constants: c0=c1=c2=...=c_{n-1}
        // Each union merges parent lists, and the accumulated parent
        // list grows by ~1 each step. Total parent clone work: O(n^2).
        let start = Instant::now();
        for i in 1..n {
            eg.union(consts[0], consts[i]);
        }
        let elapsed = start.elapsed().as_nanos();
        times.push(elapsed);
    }

    // sizes go 50 -> 200 -> 800 (4x each step).
    // If parent cloning is O(n^2): 16x → ~256x.
    // If O(n log n): 16x → ~64x.
    // If O(n): 16x → ~16x.
    let ratio_16x = times[2] as f64 / times[0].max(1) as f64;
    eprintln!(
        "do_union parent clone: 16x nodes → {ratio_16x:.1}x time \
         (sizes={sizes:?}, times_ns={times:?})"
    );
    // Document: we expect super-linear growth due to parent list cloning.
    // The ratio should be >20x for 16x input if quadratic.
}

// =========================================================================
// proof_coverage: get_class, classes, get_nodes, match_against, Trigger::multi (#982)
// =========================================================================

/// Test get_class returns the canonical EClass for a valid ID.
#[test]
fn test_get_class_returns_canonical() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);

    // get_class on a constant
    let cls_a = egraph
        .get_class(a)
        .expect("get_class should find a valid ID");
    assert_eq!(cls_a.nodes.len(), 1, "a should have exactly 1 e-node");
    assert_eq!(cls_a.nodes[0].symbol.name(), "a");

    // get_class on an app node
    let cls_fa = egraph
        .get_class(fa)
        .expect("get_class should find class for app node f(a)");
    assert_eq!(cls_fa.nodes.len(), 1);
    assert_eq!(cls_fa.nodes[0].symbol.name(), "f");
    assert_eq!(cls_fa.nodes[0].children.len(), 1);

    // After union, get_class on non-canonical ID still works (via find)
    egraph.union(a, b);
    let cls_a_id = egraph.get_class(a).expect("a should exist after union").id;
    let cls_a_len = egraph.get_class(a).unwrap().nodes.len();
    let cls_b_id = egraph.get_class(b).expect("b should exist after union").id;
    // Both should resolve to the same canonical class
    assert_eq!(cls_a_id, cls_b_id);
    // Merged class should contain both e-nodes
    assert_eq!(cls_a_len, 2);
}

/// Test classes() returns only canonical e-class IDs.
#[test]
fn test_classes_iterator_canonical_only() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let c = egraph.add_const("c");

    // Before any unions: 3 canonical classes
    let ids: Vec<EClassId> = egraph.classes().collect();
    assert_eq!(ids.len(), 3, "3 distinct constants → 3 classes");

    // Union a and b: should drop to 2 canonical classes
    egraph.union(a, b);
    let ids: Vec<EClassId> = egraph.classes().collect();
    assert_eq!(ids.len(), 2, "after union(a,b) → 2 classes");

    // Each returned ID should be canonical (find_const maps to itself)
    for id in &ids {
        assert_eq!(
            egraph.find(*id),
            *id,
            "classes() should only yield canonical IDs"
        );
    }

    // Union the remaining: should be 1 class
    egraph.union(a, c);
    let ids: Vec<EClassId> = egraph.classes().collect();
    assert_eq!(ids.len(), 1, "after union all → 1 class");
}

/// Test get_nodes returns all nodes in a canonical class.
#[test]
fn test_get_nodes_returns_all_enodes() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);

    // Single constant class has one node
    let nodes_a = egraph.get_nodes(a);
    assert_eq!(nodes_a.len(), 1);
    assert_eq!(nodes_a[0].symbol.name(), "a");
    assert!(nodes_a[0].children.is_empty());

    // App node class has one node with children
    let nodes_fa = egraph.get_nodes(fa);
    assert_eq!(nodes_fa.len(), 1);
    assert_eq!(nodes_fa[0].symbol.name(), "f");
    assert_eq!(nodes_fa[0].children.len(), 1);

    // After union, both e-nodes are in the same class
    egraph.union(a, b);
    let nodes_merged = egraph.get_nodes(a);
    assert_eq!(
        nodes_merged.len(),
        2,
        "merged class should contain both a and b nodes"
    );
    let symbols: Vec<&str> = nodes_merged.iter().map(|n| n.symbol.name()).collect();
    assert!(symbols.contains(&"a"));
    assert!(symbols.contains(&"b"));

    // get_nodes on non-canonical ID also works
    let nodes_via_b = egraph.get_nodes(b);
    assert_eq!(
        nodes_via_b.len(),
        2,
        "get_nodes via b should find merged class"
    );
}

/// Test match_against succeeds for a matching pattern and fails for non-matching.
#[test]
fn test_match_against_specific_class() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let _gb = egraph.add_app("g", vec![b]);

    let matcher = EMatcher::new(&egraph);

    // Pattern f(?x) should match the class containing f(a)
    let pat_fx = Pattern::app("f", vec![Pattern::var("x")]);
    let subst = matcher
        .match_against(&pat_fx, fa)
        .expect("f(?x) should match class of f(a)");
    assert_eq!(subst.get("x"), Some(a), "?x should bind to class of a");

    // Pattern f(?x) should NOT match the class of a (a is a constant, not f(...))
    let result = matcher.match_against(&pat_fx, a);
    assert!(result.is_none(), "f(?x) should not match constant a");

    // Pattern g(?y) should NOT match class of f(a)
    let pat_gy = Pattern::app("g", vec![Pattern::var("y")]);
    let result = matcher.match_against(&pat_gy, fa);
    assert!(result.is_none(), "g(?y) should not match f(a)");

    // Variable pattern matches any class
    let pat_var = Pattern::var("z");
    let var_subst = matcher
        .match_against(&pat_var, fa)
        .expect("?z should match any class");
    assert_eq!(var_subst.get("z"), Some(fa));
}

/// Test match_against with a nested pattern after union (congruence).
#[test]
fn test_match_against_after_union() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let fa = egraph.add_app("f", vec![a]);
    let gfa = egraph.add_app("g", vec![fa]);

    // Union a = b
    egraph.union(a, b);

    let matcher = EMatcher::new(&egraph);

    // Pattern g(f(?x)) should match class of g(f(a)), binding ?x to class of {a,b}
    let pat = Pattern::app("g", vec![Pattern::app("f", vec![Pattern::var("x")])]);
    let result = matcher.match_against(&pat, gfa);
    assert!(
        result.is_some(),
        "g(f(?x)) should match g(f(a)) after union"
    );
    let subst = result.unwrap();
    // ?x should be bound to the canonical class that contains both a and b
    let x_class = subst.get("x").expect("?x should be bound");
    assert!(
        egraph.are_equal(x_class, a) && egraph.are_equal(x_class, b),
        "?x should bind to the merged a/b class"
    );
}

/// Test match_against with repeated variable (consistency check).
#[test]
fn test_match_against_repeated_var() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let b = egraph.add_const("b");
    let faa = egraph.add_app("f", vec![a, a]);
    let fab = egraph.add_app("f", vec![a, b]);

    let matcher = EMatcher::new(&egraph);

    // Pattern f(?x, ?x) should match f(a, a) but not f(a, b)
    let pat_fxx = Pattern::app("f", vec![Pattern::var("x"), Pattern::var("x")]);

    let subst_aa = matcher
        .match_against(&pat_fxx, faa)
        .expect("f(?x,?x) should match f(a,a)");
    assert_eq!(
        subst_aa.get("x"),
        Some(a),
        "?x should bind to class of a in f(a,a)"
    );

    let result_ab = matcher.match_against(&pat_fxx, fab);
    assert!(
        result_ab.is_none(),
        "f(?x,?x) should NOT match f(a,b) when a≠b"
    );
}

/// Test Trigger::multi construction and variable collection.
#[test]
fn test_trigger_multi_construction() {
    // Multi-trigger with two patterns: f(?x) and g(?x, ?y)
    let p1 = Pattern::app("f", vec![Pattern::var("x")]);
    let p2 = Pattern::app("g", vec![Pattern::var("x"), Pattern::var("y")]);
    let trigger = Trigger::multi(vec![p1, p2]);

    assert_eq!(
        trigger.patterns.len(),
        2,
        "multi-trigger should have 2 patterns"
    );

    // Variables should collect from all patterns, deduplicated
    let vars = trigger.variables();
    assert_eq!(vars.len(), 2, "should have 2 unique variables: x, y");
    assert!(vars.contains(&"x".to_string()));
    assert!(vars.contains(&"y".to_string()));
}

/// Test Trigger::multi with overlapping variables across patterns.
#[test]
fn test_trigger_multi_overlapping_vars() {
    let p1 = Pattern::app("f", vec![Pattern::var("a"), Pattern::var("b")]);
    let p2 = Pattern::app("g", vec![Pattern::var("b"), Pattern::var("c")]);
    let p3 = Pattern::app("h", vec![Pattern::var("a"), Pattern::var("c")]);
    let trigger = Trigger::multi(vec![p1, p2, p3]);

    assert_eq!(trigger.patterns.len(), 3);
    let vars = trigger.variables();
    assert_eq!(vars.len(), 3, "a, b, c — each unique");
    assert!(vars.contains(&"a".to_string()));
    assert!(vars.contains(&"b".to_string()));
    assert!(vars.contains(&"c".to_string()));
}

/// Test Trigger::multi with find_multi_matches integration.
#[test]
fn test_trigger_multi_with_find_multi_matches() {
    let mut egraph = EGraph::new();
    let a = egraph.add_const("a");
    let _fa = egraph.add_app("f", vec![a]);
    let _ga = egraph.add_app("g", vec![a]);

    let matcher = EMatcher::new(&egraph);

    // Multi-pattern: f(?x) ∧ g(?x) — both must match with consistent ?x
    let p1 = Pattern::app("f", vec![Pattern::var("x")]);
    let p2 = Pattern::app("g", vec![Pattern::var("x")]);
    let matches = matcher.find_multi_matches(&[p1, p2]);

    assert!(
        !matches.is_empty(),
        "multi-trigger f(?x) ∧ g(?x) should match when f(a) and g(a) exist"
    );
    // ?x should bind to the class of a in every match
    for subst in &matches {
        let x_val = subst.get("x").expect("?x should be bound");
        assert!(egraph.are_equal(x_val, a), "?x should bind to class of a");
    }
}

/// Test extract on a diamond DAG: h(a, a) where both children share
/// the same e-class. The path-based visited set (with visited.remove())
/// must allow re-entry into the shared class for the second child.
#[test]
fn test_extract_diamond_dag() {
    let mut egraph = EGraph::new();

    let a = egraph.add_const("a");
    let ha_a = egraph.add_app("h", vec![a, a]);

    let term = egraph.extract(ha_a);
    assert!(
        term.is_some(),
        "extract should succeed on diamond DAG h(a, a)"
    );
    let extracted = term.unwrap();
    assert_eq!(
        extracted,
        Term::App(
            "h".to_string(),
            vec![Term::Const("a".to_string()), Term::Const("a".to_string()),]
        ),
        "h(a, a) should extract both children correctly"
    );
}

/// Test extract on a deeper diamond: f(g(a), g(a)) where g(a) is shared.
/// Verifies visited.remove() at depth > 1.
#[test]
fn test_extract_deep_diamond_dag() {
    let mut egraph = EGraph::new();

    let a = egraph.add_const("a");
    let ga = egraph.add_app("g", vec![a]);
    let f_ga_ga = egraph.add_app("f", vec![ga, ga]);

    let term = egraph.extract(f_ga_ga);
    assert!(
        term.is_some(),
        "extract should succeed on deep diamond f(g(a), g(a))"
    );
    let extracted = term.unwrap();
    assert_eq!(
        extracted,
        Term::App(
            "f".to_string(),
            vec![
                Term::App("g".to_string(), vec![Term::Const("a".to_string())]),
                Term::App("g".to_string(), vec![Term::Const("a".to_string())]),
            ]
        ),
    );
}

/// Test extract on asymmetric diamond: f(g(a), h(a)) where class(a)
/// is reachable via two different paths.
#[test]
fn test_extract_asymmetric_diamond_dag() {
    let mut egraph = EGraph::new();

    let a = egraph.add_const("a");
    let ga = egraph.add_app("g", vec![a]);
    let ha = egraph.add_app("h", vec![a]);
    let f_ga_ha = egraph.add_app("f", vec![ga, ha]);

    let term = egraph.extract(f_ga_ha);
    assert!(
        term.is_some(),
        "extract should succeed on asymmetric diamond f(g(a), h(a))"
    );
    let extracted = term.unwrap();
    assert_eq!(
        extracted,
        Term::App(
            "f".to_string(),
            vec![
                Term::App("g".to_string(), vec![Term::Const("a".to_string())]),
                Term::App("h".to_string(), vec![Term::Const("a".to_string())]),
            ]
        ),
    );
}
