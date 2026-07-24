// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// SPDX-License-Identifier: Apache-2.0

//! Tests for extended structure extension elaboration.

use crate::structure_cmd::{elaborate_structure, StructDef, StructField};
use crate::structure_extend_ext::{
    ancestor_set, elaborate_extend_ext, flatten_all_parents, has_diamond, DiagnosticKind,
    ExtendConfig, ExtendExtError, FieldOrigin,
};
use clean_kernel::{BinderInfo, Environment, Expr, Level, Name};

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn nat_type(env: &mut Environment) -> Expr {
    if env.get_inductive(&Name::from_string("Nat")).is_none() {
        env.init_nat().ok();
    }
    Expr::const_(Name::from_string("Nat"), vec![])
}

fn simple_field(name: &str, type_: Expr) -> StructField {
    StructField {
        name: Name::from_string(name),
        type_,
        default_value: None,
        binder_info: BinderInfo::Default,
        auto_param: false,
    }
}

fn field_with_default(name: &str, type_: Expr, default: Expr) -> StructField {
    StructField {
        name: Name::from_string(name),
        type_,
        default_value: Some(default),
        binder_info: BinderInfo::Default,
        auto_param: false,
    }
}

fn simple_struct(name: &str, fields: Vec<StructField>) -> StructDef {
    StructDef {
        name: Name::from_string(name),
        universe_params: vec![],
        params: vec![],
        fields,
        parents: vec![],
        is_class: false,
    }
}

fn register_struct(env: &mut Environment, name: &str, fields: Vec<StructField>) {
    elaborate_structure(&simple_struct(name, fields), env)
        .unwrap_or_else(|e| panic!("failed to elaborate {name}: {e}"));
}

fn default_config() -> ExtendConfig {
    ExtendConfig::default()
}

fn run_extend(
    name: &str,
    parents: &[&str],
    own_fields: &[StructField],
    env: &Environment,
    config: &ExtendConfig,
) -> Result<crate::structure_extend_ext::ExtendExtResult, ExtendExtError> {
    let parent_names: Vec<Name> = parents.iter().map(|p| Name::from_string(p)).collect();
    elaborate_extend_ext(
        &Name::from_string(name),
        &[],
        &[],
        own_fields,
        &parent_names,
        env,
        config,
    )
}

// ---------------------------------------------------------------------------
// 1. No parents (fast path)
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_no_parents_returns_own_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    let own = vec![simple_field("x", nat)];
    let config = default_config();

    let result = run_extend("Solo", &[], &own, &env, &config).expect("should succeed");
    assert_eq!(result.fields.len(), 1);
    assert_eq!(result.fields[0].name, Name::from_string("x"));
    assert_eq!(result.fields[0].origin, FieldOrigin::Own);
    assert!(result.projections.is_empty());
    assert!(result.coercions.is_empty());
    assert!(result.diamonds.is_empty());
    assert!(result.diagnostics.is_empty());
}

// ---------------------------------------------------------------------------
// 2. Single parent basic
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_single_parent_inherits_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Base", vec![simple_field("a", nat.clone())]);

    let own = vec![simple_field("b", nat)];
    let config = default_config();
    let result = run_extend("Child", &["Base"], &own, &env, &config).expect("resolve");

    assert_eq!(result.fields.len(), 2);
    assert_eq!(result.fields[0].name, Name::from_string("a"));
    assert_eq!(result.fields[1].name, Name::from_string("b"));
}

#[test]
fn test_extend_ext_single_parent_generates_projections() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "P", vec![simple_field("val", nat.clone())]);

    let own = vec![simple_field("extra", nat)];
    let config = default_config();
    let result = run_extend("C", &["P"], &own, &env, &config).expect("resolve");

    // Projections for all fields (inherited + own)
    assert_eq!(result.projections.len(), 2);
}

#[test]
fn test_extend_ext_single_parent_generates_coercions() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Src", vec![simple_field("s", nat.clone())]);

    let config = default_config();
    let result =
        run_extend("Dst", &["Src"], &[simple_field("d", nat)], &env, &config).expect("resolve");

    assert_eq!(result.coercions.len(), 1);
    let coe_name = match &result.coercions[0] {
        clean_kernel::Declaration::Definition { name, .. } => name.to_string(),
        _ => panic!("expected Definition"),
    };
    assert!(coe_name.contains("toSrc"));
}

// ---------------------------------------------------------------------------
// 3. Multiple parents
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_multiple_parents_merge_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "A", vec![simple_field("a_field", nat.clone())]);
    register_struct(&mut env, "B", vec![simple_field("b_field", nat.clone())]);

    let config = default_config();
    let result = run_extend(
        "C",
        &["A", "B"],
        &[simple_field("c_field", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert_eq!(result.fields.len(), 3);
    let names: Vec<String> = result.fields.iter().map(|f| f.name.to_string()).collect();
    assert!(names.contains(&"a_field".to_string()));
    assert!(names.contains(&"b_field".to_string()));
    assert!(names.contains(&"c_field".to_string()));
}

#[test]
fn test_extend_ext_multiple_parents_coercions() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "M1", vec![simple_field("x", nat.clone())]);
    register_struct(&mut env, "M2", vec![simple_field("y", nat.clone())]);

    let config = default_config();
    let result = run_extend(
        "M3",
        &["M1", "M2"],
        &[simple_field("z", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert_eq!(result.coercions.len(), 2);
}

// ---------------------------------------------------------------------------
// 4. Diamond detection
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_diamond_detected() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Top", vec![simple_field("root", nat.clone())]);
    register_struct(
        &mut env,
        "Left",
        vec![
            simple_field("toTop", Expr::sort(Level::succ(Level::zero()))),
            simple_field("l", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "Right",
        vec![
            simple_field("toTop", Expr::sort(Level::succ(Level::zero()))),
            simple_field("r", nat.clone()),
        ],
    );

    let config = default_config();
    let result = run_extend(
        "Bottom",
        &["Left", "Right"],
        &[simple_field("own", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert!(!result.diamonds.is_empty(), "should detect diamond");
    assert_eq!(result.diamonds[0].ancestor, Name::from_string("Top"));
}

#[test]
fn test_extend_ext_strict_diamond_errors() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Root", vec![simple_field("v", nat.clone())]);
    register_struct(
        &mut env,
        "LA",
        vec![
            simple_field("toRoot", Expr::sort(Level::succ(Level::zero()))),
            simple_field("la", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "RA",
        vec![
            simple_field("toRoot", Expr::sort(Level::succ(Level::zero()))),
            simple_field("ra", nat.clone()),
        ],
    );

    let config = ExtendConfig {
        strict_diamond: true,
        ..default_config()
    };
    let result = run_extend(
        "Dia",
        &["LA", "RA"],
        &[simple_field("d", nat)],
        &env,
        &config,
    );
    assert!(result.is_err());
    match result.unwrap_err() {
        ExtendExtError::DiamondConflict { ancestors, .. } => {
            assert!(ancestors.len() >= 2);
        }
        other => panic!("unexpected error: {other}"),
    }
}

#[test]
fn test_extend_ext_no_diamond_for_single_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Only", vec![simple_field("f", nat.clone())]);

    let config = default_config();
    let result = run_extend(
        "OnlyChild",
        &["Only"],
        &[simple_field("g", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert!(result.diamonds.is_empty());
}

// ---------------------------------------------------------------------------
// 5. Field conflict / override
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_field_override_origin_tracked() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Par", vec![simple_field("x", nat.clone())]);

    let own = vec![simple_field("x", Expr::sort(Level::zero()))];
    let config = default_config();
    let result = run_extend("Ovr", &["Par"], &own, &env, &config).expect("resolve");

    // The field should appear once, and the type should be the own type (Prop).
    assert_eq!(result.fields.len(), 1);
    assert_eq!(result.fields[0].type_expr, Expr::sort(Level::zero()));
}

// ---------------------------------------------------------------------------
// 6. Default value propagation
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_own_default_value_preserved() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Cfg", vec![simple_field("width", nat.clone())]);

    let own = vec![field_with_default("height", nat, Expr::nat_lit(42))];
    let config = default_config();
    let result = run_extend("Screen", &["Cfg"], &own, &env, &config).expect("resolve");

    let height = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("height"))
        .unwrap();
    assert!(height.default_value.is_some());
    assert_eq!(height.default_value.as_ref().unwrap(), &Expr::nat_lit(42));
}

#[test]
fn test_extend_ext_propagation_disabled_no_inherited_defaults() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "NoD", vec![simple_field("f", nat.clone())]);

    let config = ExtendConfig {
        propagate_defaults: false,
        ..default_config()
    };
    let result = run_extend(
        "NoDChild",
        &["NoD"],
        &[simple_field("g", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    // With propagation disabled, inherited fields should not carry defaults.
    for field in &result.fields {
        if field.name == Name::from_string("f") {
            assert!(field.default_value.is_none());
        }
    }
}

// ---------------------------------------------------------------------------
// 7. Eta expansion
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_eta_expansion_generated() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "EtaP", vec![simple_field("ep", nat.clone())]);

    let config = default_config();
    let result =
        run_extend("EtaC", &["EtaP"], &[simple_field("ec", nat)], &env, &config).expect("resolve");

    assert_eq!(result.eta_expansions.len(), 1);
    let eta_name = match &result.eta_expansions[0] {
        clean_kernel::Declaration::Definition { name, .. } => name.to_string(),
        _ => panic!("expected Definition"),
    };
    assert!(eta_name.contains("etaEtaP"));
}

#[test]
fn test_extend_ext_eta_expansion_disabled() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "NoEta", vec![simple_field("f", nat.clone())]);

    let config = ExtendConfig {
        generate_eta: false,
        ..default_config()
    };
    let result = run_extend(
        "NoEtaC",
        &["NoEta"],
        &[simple_field("g", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert!(result.eta_expansions.is_empty());
}

// ---------------------------------------------------------------------------
// 8. Circularity detection
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_circular_detected() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Circ", vec![simple_field("c", nat)]);

    let config = default_config();
    let result = run_extend("Circ", &["Circ"], &[], &env, &config);
    assert!(result.is_err());
    match result.unwrap_err() {
        ExtendExtError::CircularExtension { .. } => {}
        other => panic!("unexpected error: {other}"),
    }
}

// ---------------------------------------------------------------------------
// 9. Unknown parent
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_unknown_parent_error() {
    let env = Environment::new();
    let config = default_config();
    let result = run_extend("X", &["NonExistent"], &[], &env, &config);
    assert!(result.is_err());
}

// ---------------------------------------------------------------------------
// 10. Diagnostics
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_coercion_diagnostic_emitted() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "DiagP", vec![simple_field("dp", nat.clone())]);

    let config = default_config();
    let result = run_extend(
        "DiagC",
        &["DiagP"],
        &[simple_field("dc", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    let coe_diags: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.kind == DiagnosticKind::CoercionGenerated)
        .collect();
    assert!(!coe_diags.is_empty(), "should have coercion diagnostic");
}

#[test]
fn test_extend_ext_diamond_diagnostic_emitted() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "DD", vec![simple_field("v", nat.clone())]);
    register_struct(
        &mut env,
        "DL",
        vec![
            simple_field("toDD", Expr::sort(Level::succ(Level::zero()))),
            simple_field("dl", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "DR",
        vec![
            simple_field("toDD", Expr::sort(Level::succ(Level::zero()))),
            simple_field("dr", nat.clone()),
        ],
    );

    let config = default_config();
    let result = run_extend(
        "DB",
        &["DL", "DR"],
        &[simple_field("b", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    let diamond_diags: Vec<_> = result
        .diagnostics
        .iter()
        .filter(|d| d.kind == DiagnosticKind::DiamondDetected)
        .collect();
    assert!(!diamond_diags.is_empty(), "should have diamond diagnostic");
}

// ---------------------------------------------------------------------------
// 11. has_diamond helper
// ---------------------------------------------------------------------------

#[test]
fn test_has_diamond_helper_true() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "HD", vec![simple_field("h", nat.clone())]);
    register_struct(
        &mut env,
        "HL",
        vec![
            simple_field("toHD", Expr::sort(Level::succ(Level::zero()))),
            simple_field("hl", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "HR",
        vec![
            simple_field("toHD", Expr::sort(Level::succ(Level::zero()))),
            simple_field("hr", nat),
        ],
    );

    let parents = [Name::from_string("HL"), Name::from_string("HR")];
    assert!(has_diamond(&parents, &env));
}

#[test]
fn test_has_diamond_helper_false_single_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "NoDia", vec![simple_field("nd", nat)]);

    let parents = [Name::from_string("NoDia")];
    assert!(!has_diamond(&parents, &env));
}

// ---------------------------------------------------------------------------
// 12. flatten_all_parents helper
// ---------------------------------------------------------------------------

#[test]
fn test_flatten_all_parents_basic() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "FP",
        vec![simple_field("fa", nat.clone()), simple_field("fb", nat)],
    );

    let parents = [Name::from_string("FP")];
    let flat = flatten_all_parents(&parents, &env).expect("flatten");
    assert_eq!(flat.len(), 2);
}

// ---------------------------------------------------------------------------
// 13. ancestor_set helper
// ---------------------------------------------------------------------------

#[test]
fn test_ancestor_set_transitive() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "G", vec![simple_field("g", nat.clone())]);
    register_struct(
        &mut env,
        "H",
        vec![
            simple_field("toG", Expr::sort(Level::succ(Level::zero()))),
            simple_field("h", nat),
        ],
    );

    let parents = [Name::from_string("H")];
    let ancestors = ancestor_set(&parents, &env);
    assert!(ancestors.contains(&Name::from_string("G")));
}

#[test]
fn test_ancestor_set_empty_for_no_parents() {
    let env = Environment::new();
    let ancestors = ancestor_set(&[], &env);
    assert!(ancestors.is_empty());
}

// ---------------------------------------------------------------------------
// 14. Config max_depth
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_max_depth_respected() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Deep", vec![simple_field("d", nat.clone())]);

    let config = ExtendConfig {
        max_depth: 0,
        ..default_config()
    };
    // With max_depth=0, no transitive ancestors are collected, so no diamonds.
    let result = run_extend(
        "Shallow",
        &["Deep"],
        &[simple_field("s", nat)],
        &env,
        &config,
    )
    .expect("resolve");
    assert!(result.diamonds.is_empty());
}

// ---------------------------------------------------------------------------
// 15. Empty own fields with parent
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_empty_own_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "OnlyP", vec![simple_field("p", nat)]);

    let config = default_config();
    let result = run_extend("OnlyInherited", &["OnlyP"], &[], &env, &config).expect("resolve");

    assert_eq!(result.fields.len(), 1);
    assert_eq!(result.fields[0].name, Name::from_string("p"));
}

// ---------------------------------------------------------------------------
// 16. Empty parent structure
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_empty_parent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "EmptyP", vec![]);

    let config = default_config();
    let result = run_extend(
        "FromEmpty",
        &["EmptyP"],
        &[simple_field("own", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert_eq!(result.fields.len(), 1);
    assert_eq!(result.fields[0].origin, FieldOrigin::Own);
}

// ---------------------------------------------------------------------------
// 17. Field ordering preserved
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_field_ordering() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Ordered",
        vec![
            simple_field("first", nat.clone()),
            simple_field("second", nat.clone()),
        ],
    );

    let own = vec![simple_field("third", nat)];
    let config = default_config();
    let result = run_extend("OrderedChild", &["Ordered"], &own, &env, &config).expect("resolve");

    let names: Vec<String> = result.fields.iter().map(|f| f.name.to_string()).collect();
    assert_eq!(names, vec!["first", "second", "third"]);
}

// ---------------------------------------------------------------------------
// 18. Inherited field origin tracking
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_inherited_origin_tracked() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Tracker",
        vec![simple_field("tracked", nat.clone())],
    );

    let config = default_config();
    let result = run_extend(
        "Dest",
        &["Tracker"],
        &[simple_field("local", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    let tracked = result
        .fields
        .iter()
        .find(|f| f.name == Name::from_string("tracked"))
        .unwrap();
    match &tracked.origin {
        FieldOrigin::Inherited { parent } => {
            assert_eq!(*parent, Name::from_string("Tracker"));
        }
        other => panic!("expected Inherited, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// 19. Multiple parents field indices
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_multiple_parents_all_projections() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "P1", vec![simple_field("p1f", nat.clone())]);
    register_struct(&mut env, "P2", vec![simple_field("p2f", nat.clone())]);

    let config = default_config();
    let result = run_extend(
        "Kid",
        &["P1", "P2"],
        &[simple_field("kid", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    // 3 fields = 3 projections
    assert_eq!(result.projections.len(), 3);
}

// ---------------------------------------------------------------------------
// 20. Default config values
// ---------------------------------------------------------------------------

#[test]
fn test_extend_config_defaults() {
    let config = ExtendConfig::default();
    assert_eq!(config.max_depth, 64);
    assert!(!config.strict_diamond);
    assert!(config.propagate_defaults);
    assert!(config.generate_eta);
}

// ---------------------------------------------------------------------------
// 21. Diamond info contains shared fields
// ---------------------------------------------------------------------------

#[test]
fn test_diamond_info_shared_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Shared",
        vec![simple_field("common", nat.clone())],
    );
    register_struct(
        &mut env,
        "DiaL",
        vec![
            simple_field("toShared", Expr::sort(Level::succ(Level::zero()))),
            simple_field("left", nat.clone()),
        ],
    );
    register_struct(
        &mut env,
        "DiaR",
        vec![
            simple_field("toShared", Expr::sort(Level::succ(Level::zero()))),
            simple_field("right", nat.clone()),
        ],
    );

    let config = default_config();
    let result = run_extend(
        "DiaBot",
        &["DiaL", "DiaR"],
        &[simple_field("b", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert!(!result.diamonds.is_empty());
    let di = &result.diamonds[0];
    assert!(!di.shared_fields.is_empty());
    assert!(di.shared_fields.contains(&Name::from_string("common")));
}

// ---------------------------------------------------------------------------
// 22. Multiple eta expansions for multiple parents
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_multiple_eta_expansions() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "EP1", vec![simple_field("e1", nat.clone())]);
    register_struct(&mut env, "EP2", vec![simple_field("e2", nat.clone())]);

    let config = default_config();
    let result = run_extend(
        "EC",
        &["EP1", "EP2"],
        &[simple_field("e3", nat)],
        &env,
        &config,
    )
    .expect("resolve");

    assert_eq!(result.eta_expansions.len(), 2);
}

// ---------------------------------------------------------------------------
// 23. Projection count matches field count
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_projection_count_matches_fields() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(
        &mut env,
        "Big",
        vec![
            simple_field("a", nat.clone()),
            simple_field("b", nat.clone()),
            simple_field("c", nat.clone()),
        ],
    );

    let config = default_config();
    let result =
        run_extend("Bigger", &["Big"], &[simple_field("d", nat)], &env, &config).expect("resolve");

    assert_eq!(result.fields.len(), 4);
    assert_eq!(result.projections.len(), 4);
}

// ---------------------------------------------------------------------------
// 24. ExtendExtError display
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_error_display() {
    let err = ExtendExtError::DiamondConflict {
        field: Name::from_string("val"),
        ancestors: vec![Name::from_string("A"), Name::from_string("B")],
    };
    let msg = err.to_string();
    assert!(msg.contains("diamond"));
    assert!(msg.contains("val"));
}

#[test]
fn test_extend_ext_circular_error_display() {
    let err = ExtendExtError::CircularExtension {
        detail: "Foo extends Foo".to_string(),
    };
    assert!(err.to_string().contains("circular"));
}

// ---------------------------------------------------------------------------
// 25. Resolved field binder info default
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_resolved_field_binder_info() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "BI", vec![simple_field("f", nat.clone())]);

    let config = default_config();
    let result =
        run_extend("BIC", &["BI"], &[simple_field("g", nat)], &env, &config).expect("resolve");

    for field in &result.fields {
        assert_eq!(field.binder_info, BinderInfo::Default);
    }
}

// ---------------------------------------------------------------------------
// 26. Idempotent resolution
// ---------------------------------------------------------------------------

#[test]
fn test_extend_ext_idempotent() {
    let mut env = Environment::new();
    let nat = nat_type(&mut env);
    register_struct(&mut env, "Idem", vec![simple_field("v", nat.clone())]);

    let own = vec![simple_field("w", nat)];
    let config = default_config();
    let r1 = run_extend("T", &["Idem"], &own, &env, &config).expect("first");
    let r2 = run_extend("T", &["Idem"], &own, &env, &config).expect("second");

    assert_eq!(r1.fields.len(), r2.fields.len());
    assert_eq!(r1.projections.len(), r2.projections.len());
    assert_eq!(r1.coercions.len(), r2.coercions.len());
    assert_eq!(r1.diamonds.len(), r2.diamonds.len());
}
