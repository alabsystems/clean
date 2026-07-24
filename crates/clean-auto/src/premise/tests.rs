// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use clean_kernel::{Expr, Level, Name};

fn name(s: &str) -> Name {
    s.parse().unwrap()
}

fn make_const(s: &str) -> Expr {
    Expr::const_(name(s), vec![])
}

fn make_app(f: &str, arg: Expr) -> Expr {
    Expr::app(make_const(f), arg)
}

fn make_app2(f: &str, arg1: Expr, arg2: Expr) -> Expr {
    Expr::app(Expr::app(make_const(f), arg1), arg2)
}

#[test]
fn test_feature_extraction_constant() {
    let expr = make_const("Nat.add");
    let extractor = FeatureExtractor::new();
    let features = extractor.extract(&expr);

    assert!(features
        .features()
        .contains(&Feature::Const(name("Nat.add"))));
    assert!(features
        .features()
        .contains(&Feature::Theory("arith".to_string())));
}

#[test]
fn test_feature_extraction_application() {
    let expr = make_app2("Nat.add", make_const("x"), make_const("y"));
    let extractor = FeatureExtractor::new();
    let features = extractor.extract(&expr);

    assert!(features
        .features()
        .contains(&Feature::Const(name("Nat.add"))));
    assert!(features.features().contains(&Feature::Const(name("x"))));
    assert!(features.features().contains(&Feature::Const(name("y"))));
    assert!(features.features().contains(&Feature::App(name("Nat.add"))));
    assert!(features
        .features()
        .contains(&Feature::BinApp(name("Nat.add"))));
}

#[test]
fn test_feature_extraction_pi() {
    // ∀ x : Nat, P x
    let nat = make_const("Nat");
    let p_x = make_app("P", Expr::bvar(0));
    let expr = Expr::pi(clean_kernel::BinderInfo::Default, nat, p_x);

    let extractor = FeatureExtractor::new();
    let features = extractor.extract(&expr);

    assert!(features.features().contains(&Feature::Const(name("Nat"))));
    assert!(features.features().contains(&Feature::Const(name("P"))));
}

#[test]
fn test_extract_constants() {
    let expr = make_app2("f", make_const("a"), make_app("g", make_const("b")));
    let extractor = FeatureExtractor::new();
    let constants = extractor.extract_constants(&expr);

    assert!(constants.contains(&name("f")));
    assert!(constants.contains(&name("a")));
    assert!(constants.contains(&name("g")));
    assert!(constants.contains(&name("b")));
    assert_eq!(constants.len(), 4);
}

#[test]
fn test_feature_set_overlap() {
    let mut fs1 = FeatureSet::new();
    fs1.add(Feature::Const(name("a")));
    fs1.add(Feature::Const(name("b")));
    fs1.add(Feature::Const(name("c")));

    let mut fs2 = FeatureSet::new();
    fs2.add(Feature::Const(name("b")));
    fs2.add(Feature::Const(name("c")));
    fs2.add(Feature::Const(name("d")));

    assert_eq!(fs1.overlap(&fs2), 2); // b and c
}

#[test]
fn test_score_sort_nan_last_and_id_tiebreak() {
    let mut scored = vec![
        (PremiseId(2), 1.0),
        (PremiseId(1), 1.0),
        (PremiseId(3), f64::NAN),
    ];

    scored.sort_by(|a, b| cmp_score_desc_then_id(a.1, a.0, b.1, b.0));

    let ids: Vec<_> = scored.into_iter().map(|(id, _)| id.0).collect();
    assert_eq!(ids, vec![1, 2, 3]);
}

#[test]
fn test_feature_set_jaccard() {
    let mut fs1 = FeatureSet::new();
    fs1.add(Feature::Const(name("a")));
    fs1.add(Feature::Const(name("b")));

    let mut fs2 = FeatureSet::new();
    fs2.add(Feature::Const(name("b")));
    fs2.add(Feature::Const(name("c")));

    // Intersection: {b}, Union: {a, b, c}
    // Jaccard = 1/3
    let jaccard = fs1.jaccard(&fs2);
    assert!((jaccard - 1.0 / 3.0).abs() < 0.001);
}

#[test]
fn test_premise_database() {
    let mut db = PremiseDatabase::new();

    let stmt1 = make_app2("Eq", make_const("a"), make_const("a"));
    let id1 = db.add(name("refl"), stmt1);

    let stmt2 = make_app2("Eq", make_const("a"), make_const("b"));
    let _id2 = db.add(name("hyp"), stmt2);

    assert_eq!(db.len(), 2);
    assert!(
        db.get(id1).is_some(),
        "premise database should contain entry by id {id1:?}"
    );
    assert!(
        db.get_by_name(&name("refl")).is_some(),
        "premise database should contain entry by name 'refl'"
    );

    // Check constant frequencies
    assert_eq!(db.const_frequency(&name("Eq")), 2);
    assert_eq!(db.const_frequency(&name("a")), 2);
    assert_eq!(db.const_frequency(&name("b")), 1);
}

#[test]
fn test_mepo_selection() {
    let mut db = PremiseDatabase::new();

    // Add premises with different symbol profiles
    db.add(
        name("nat_add_comm"),
        make_app2("Nat.add", make_const("x"), make_const("y")),
    );
    db.add(
        name("nat_mul_comm"),
        make_app2("Nat.mul", make_const("x"), make_const("y")),
    );
    db.add(
        name("list_length"),
        make_app("List.length", make_const("xs")),
    );

    // Goal involving Nat.add
    let goal = make_app2("Nat.add", make_const("a"), make_const("b"));

    let selector = MePoSelector::new(&db).with_threshold(0.0);
    let selected = selector.select_with_scores(&goal);

    // nat_add_comm should rank highest (shares Nat.add)
    assert!(!selected.is_empty());
    assert_eq!(selected[0].0.name, name("nat_add_comm"));
}

#[test]
fn test_mepo_rare_symbol_weight() {
    let mut db = PremiseDatabase::new();

    // Add many premises with common symbol
    for i in 0..10 {
        db.add(
            name(&format!("common_{i}")),
            make_app("common_fn", make_const(&format!("x{i}"))),
        );
    }

    // Add one premise with rare symbol
    db.add(name("rare_one"), make_app("rare_fn", make_const("x")));

    // Goal with both rare and common symbols
    let _goal = make_app2("combine", make_const("rare_fn"), make_const("common_fn"));

    let selector = MePoSelector::new(&db);

    // rare_fn weight should be higher than common_fn weight
    let rare_weight = selector.const_weight(&name("rare_fn"));
    let common_weight = selector.const_weight(&name("common_fn"));

    assert!(rare_weight > common_weight);
}

#[test]
fn test_mash_without_history() {
    let mut db = PremiseDatabase::new();

    db.add(name("p1"), make_app("f", make_const("a")));
    db.add(name("p2"), make_app("g", make_const("b")));

    let goal = make_app("f", make_const("x"));

    let selector = MaShSelector::new(&db);
    let selected = selector.select(&goal);

    // Should fall back to feature similarity
    // p1 should rank higher (shares "f")
    assert!(!selected.is_empty());
}

#[test]
fn test_mash_with_history() {
    let mut db = PremiseDatabase::new();

    let id1 = db.add(name("p1"), make_app("f", make_const("a")));
    let id2 = db.add(name("p2"), make_app("g", make_const("b")));
    let _id3 = db.add(name("p3"), make_app("h", make_const("c")));

    let mut selector = MaShSelector::new(&db);

    // Record that p1 and p2 were useful for a goal involving f
    let past_goal = make_app("f", make_const("x"));
    selector.record_proof(&past_goal, vec![id1, id2]);

    // New goal also involving f
    let new_goal = make_app("f", make_const("y"));
    let selected = selector.select(&new_goal);

    // p1 and p2 should be recommended based on history
    let selected_ids: Vec<_> = selected.iter().map(|p| p.id).collect();
    assert!(selected_ids.contains(&id1) || selected_ids.contains(&id2));
}

#[test]
fn test_hybrid_selector() {
    let mut db = PremiseDatabase::new();

    let id1 = db.add(
        name("eq_refl"),
        make_app2("Eq", make_const("x"), make_const("x")),
    );
    let _id2 = db.add(
        name("eq_symm"),
        make_app2("Eq", make_const("y"), make_const("x")),
    );
    let _id3 = db.add(
        name("nat_add"),
        make_app2("Nat.add", make_const("a"), make_const("b")),
    );

    let mut selector = HybridSelector::new(&db)
        .with_mepo_weight(0.6)
        .with_mash_weight(0.4);

    // Record a proof
    let past_goal = make_app2("Eq", make_const("a"), make_const("a"));
    selector.record_proof(&past_goal, vec![id1]);

    // Select for new goal
    let goal = make_app2("Eq", make_const("p"), make_const("q"));
    let selected = selector.select(&goal);

    // eq_refl and eq_symm should rank higher than nat_add
    assert!(!selected.is_empty());
    let top_name = &selected[0].name;
    assert!(
        *top_name == name("eq_refl") || *top_name == name("eq_symm"),
        "Expected eq_refl or eq_symm, got {top_name:?}"
    );
}

#[test]
fn test_theory_detection() {
    let extractor = FeatureExtractor::new();

    let nat_expr = make_const("Nat.succ");
    let features = extractor.extract(&nat_expr);
    assert!(features
        .features()
        .contains(&Feature::Theory("arith".to_string())));

    let list_expr = make_const("List.cons");
    let features = extractor.extract(&list_expr);
    assert!(features
        .features()
        .contains(&Feature::Theory("list".to_string())));

    let set_expr = make_const("Set.union");
    let features = extractor.extract(&set_expr);
    assert!(features
        .features()
        .contains(&Feature::Theory("set".to_string())));
}

#[test]
fn test_max_depth_limiting() {
    // Create a deeply nested expression
    let mut expr = make_const("leaf");
    for i in 0..10 {
        expr = make_app(&format!("f{i}"), expr);
    }

    // With depth 2, should not extract deeply nested features
    let extractor = FeatureExtractor::new().with_depth(2);
    let features = extractor.extract(&expr);

    // Should have some but not all features
    assert!(features.len() < 11);
    assert!(features.features().contains(&Feature::Const(name("f9"))));
}

#[test]
fn test_with_types_false_skips_type_positions() {
    // ∀ x : TypeConst, Body
    let type_const = make_const("TypeConst");
    let body_const = make_const("BodyConst");
    let expr = Expr::pi(clean_kernel::BinderInfo::Default, type_const, body_const);

    // With include_types=false, should NOT extract TypeConst
    let extractor = FeatureExtractor::new().with_types(false);
    let features = extractor.extract(&expr);

    assert!(
        !features
            .features()
            .contains(&Feature::Const(name("TypeConst"))),
        "TypeConst should be skipped when include_types=false"
    );
    assert!(
        features
            .features()
            .contains(&Feature::Const(name("BodyConst"))),
        "BodyConst should still be extracted"
    );
}

#[test]
fn test_with_types_false_let_val_still_traversed() {
    // let x : Ty = Val in Body
    let ty = make_const("TyConst");
    let val = make_const("ValConst");
    let body = make_const("BodyConst");
    let expr = Expr::let_named(Name::anon(), ty, val, body, false);

    // With include_types=false, TyConst should be skipped but ValConst traversed
    let extractor = FeatureExtractor::new().with_types(false);
    let features = extractor.extract(&expr);

    assert!(
        !features
            .features()
            .contains(&Feature::Const(name("TyConst"))),
        "TyConst should be skipped when include_types=false"
    );
    assert!(
        features
            .features()
            .contains(&Feature::Const(name("ValConst"))),
        "ValConst should be extracted (value position, not type)"
    );
    assert!(
        features
            .features()
            .contains(&Feature::Const(name("BodyConst"))),
        "BodyConst should be extracted"
    );
}

#[test]
fn test_with_patterns_false_skips_app_features() {
    // f(a) - application
    let expr = make_app("f", make_const("a"));

    // With include_patterns=false, should NOT add App feature
    let extractor = FeatureExtractor::new().with_patterns(false);
    let features = extractor.extract(&expr);

    // Constants should still be extracted
    assert!(features.features().contains(&Feature::Const(name("f"))));
    assert!(features.features().contains(&Feature::Const(name("a"))));
    // But App pattern should NOT be extracted
    assert!(
        !features.features().contains(&Feature::App(name("f"))),
        "App feature should be skipped when include_patterns=false"
    );
}

#[test]
fn test_with_patterns_false_skips_binapp_features() {
    // f(a, b) - binary application
    let expr = make_app2("f", make_const("a"), make_const("b"));

    // With include_patterns=false, should NOT add App or BinApp features
    let extractor = FeatureExtractor::new().with_patterns(false);
    let features = extractor.extract(&expr);

    // Constants should still be extracted
    assert!(features.features().contains(&Feature::Const(name("f"))));
    assert!(features.features().contains(&Feature::Const(name("a"))));
    assert!(features.features().contains(&Feature::Const(name("b"))));
    // But pattern features should NOT be extracted
    assert!(
        !features.features().contains(&Feature::App(name("f"))),
        "App feature should be skipped when include_patterns=false"
    );
    assert!(
        !features.features().contains(&Feature::BinApp(name("f"))),
        "BinApp feature should be skipped when include_patterns=false"
    );
}

#[test]
fn test_empty_goal() {
    let db = PremiseDatabase::new();
    let mepo = MePoSelector::new(&db);

    // Goal with only bound variables
    let goal = Expr::lam(
        clean_kernel::BinderInfo::Default,
        Expr::sort(Level::zero()),
        Expr::bvar(0),
    );

    let selected = mepo.select(&goal);
    assert!(selected.is_empty());
}

#[test]
fn test_premise_dependencies() {
    let mut db = PremiseDatabase::new();

    let id1 = db.add(name("p1"), make_const("a"));
    let id2 = db.add(name("p2"), make_const("b"));
    let id3 = db.add(name("p3"), make_const("c"));

    // Record that p3 was proved using p1 and p2
    db.record_proof(id3, &[id1, id2]);

    let p3 = db.get(id3).unwrap();
    assert_eq!(p3.dependencies.len(), 2);
    assert!(p3.dependencies.contains(&id1));
    assert!(p3.dependencies.contains(&id2));
}
